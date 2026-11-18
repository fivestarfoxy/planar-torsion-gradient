module

public import Torsion.CanonicalGradientStability
public import Torsion.CanonicalRadialStability

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Outer radial observations on any area-one maximizer

The supporting points and frames may vary. The areas of their outer radial
domains still tend to one, because the physical thickenings have the same
areas in every isometric frame. The calibration then forces the unscaled
profiles themselves to converge to the canonical profile in angular L².
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal symmDiff

namespace Torsion.Spectral

private theorem thickening_frame_subset (D : ConvexDomain) (p n : Plane)
    (hn : ‖n‖ = 1) (r : ℝ) (hr : 0 < r) :
    thickening r (D.inNormalFrame p n hn).carrier ⊆
      ((D.gaugeOuterThickening r hr).inNormalFrame p n hn).carrier := by
  intro z hz
  obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hz
  rw [ConvexDomain.mem_inNormalFrame]
  apply mem_thickening_iff.mpr
  refine ⟨normalFrame n hn w + p, (D.mem_inNormalFrame p n w hn).mp hw, ?_⟩
  simpa only [dist_add_right, LinearIsometryEquiv.dist_map] using hzw

private theorem radialArea_eq_volumeReal (R : ContinuousProfiles.Profile)
    (hR : ∀ θ, 0 < R θ) :
    radialArea (ContinuousProfiles.extend R) =
      (volume (radialDomain (ContinuousProfiles.extend R))).toReal := by
  rw [← ContinuousProfiles.profileArea_embed]
  exact (ContinuousProfiles.geometric_area_eq_profileArea hR).symm

/-- Positive radial observations near an extremizer converge in geometric
symmetric difference even if their areas only tend to one. -/
theorem radial_observation_excess_tendsto (R : ℕ → ContinuousProfiles.Profile)
    (hR : ∀ k θ, 0 < R k θ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (harea : Tendsto (fun k => radialArea (ContinuousProfiles.extend (R k))) atTop (𝓝 1))
    (hq : ∀ k, spectralConstant secondEigenvalue secondEigenfunction * (1 - δ k) ≤
      torsionFlux (radialDomain (ContinuousProfiles.extend (R k)))) :
    Tendsto (fun k => volume (radialDomain (ContinuousProfiles.extend (R k)) \
      normalizedImage secondEigenvalue secondEigenfunction)) atTop (𝓝 0) := by
  let C := spectralConstant secondEigenvalue secondEigenfunction
  let u (k : ℕ) := ContinuousProfiles.embed (R k)
  let v := ContinuousProfiles.embed secondAreaOneRadialProfile
  have hC : 0 < C := secondMoments.sharpConstant_pos
  have hnorm (k : ℕ) : ‖u k - v‖ ^ 2 ≤
      2 * (radialArea (ContinuousProfiles.extend (R k)) - 1) + 4 * δ k := by
    have hcal := second_radial_calibration (R k) (hR k)
    rw [secondCalibrationDensity_area_one, real_inner_smul_left, real_inner_comm] at hcal
    have hinner : 1 - δ k ≤ inner (𝕜 := ℝ) (u k) v / 2 := by
      apply (mul_le_mul_iff_right₀ hC).mp
      calc
        C * (1 - δ k) ≤ _ := hq k
        _ ≤ C / 2 * inner (𝕜 := ℝ) (u k) v := hcal
        _ = _ := by ring
    have hid := norm_sub_sq_real (u k) v
    have hval : ‖u k‖ ^ 2 = 2 * radialArea (ContinuousProfiles.extend (R k)) :=
      ContinuousProfiles.norm_sq_eq_twice_radialArea (R k)
    have href : ‖v‖ ^ 2 = 2 := secondAreaOneRadialProfile_norm_sq
    nlinarith only [hid, hval, href, hinner]
  have hbound : Tendsto (fun k =>
      2 * (radialArea (ContinuousProfiles.extend (R k)) - 1) + 4 * δ k) atTop (𝓝 0) := by
    simpa using ((harea.sub_const 1).const_mul 2).add (hδ.const_mul 4)
  have hsq : Tendsto (fun k => ‖u k - v‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hnorm hbound
  have hdiff : Tendsto (fun k => ‖u k - v‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt
  have hu : Tendsto u atTop (𝓝 v) := tendsto_iff_norm_sub_tendsto_zero.mpr hdiff
  have hprod : Tendsto (fun k => (1 / 2 : ℝ) * ‖u k - v‖ * ‖u k + v‖) atTop (𝓝 0) := by
    simpa using (hdiff.const_mul (1 / 2 : ℝ)).mul (hu.add_const v).norm
  let A (k : ℕ) := radialDomain (ContinuousProfiles.extend (R k))
  let B := radialDomain (ContinuousProfiles.extend secondAreaOneRadialProfile)
  have hfin (k : ℕ) : volume (A k ∆ B) ≠ ∞ :=
    (((ContinuousProfiles.domain_isMarked (hR k)).2.1.union
      (ContinuousProfiles.domain_isMarked secondAreaOneRadialProfile_pos).2.1).subset
      Set.symmDiff_subset_union).measure_lt_top.ne
  have hsymm : Tendsto (fun k => (volume (A k ∆ B)).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg)
      (fun k => ContinuousProfiles.area_symmDiff_le_l2 (hR k) secondAreaOneRadialProfile_pos)
      hprod
  have hENN : Tendsto (fun k => volume (A k ∆ B)) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff hfin).mp hsymm
  rw [← secondAreaOneRadialProfile_domain]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hENN (fun _ => bot_le)
  intro k
  apply measure_mono
  exact fun z hz => Or.inl hz

/-- For every area-one maximizer, actual normal frames and unscaled outer
domains have vanishing area outside the canonical spectral domain. -/
theorem exists_areaOne_maximizer_outer_sequence (D : ConvexDomain) (hA : D.area = 1)
    (hG : torsionTheory.G D = ENNReal.ofReal (spectralConstant secondEigenvalue secondEigenfunction)) :
    ∃ (p n : ℕ → Plane) (hn : ∀ k, ‖n k‖ = 1) (E : ℕ → Set Plane),
      (∀ k, p k ∈ frontier D.carrier) ∧
      (∀ k, (D.inNormalFrame (p k) (n k) (hn k)).carrier ⊆ E k) ∧
      Tendsto (fun k => volume (E k \ normalizedImage secondEigenvalue secondEigenfunction))
        atTop (𝓝 0) := by
  classical
  let C := spectralConstant secondEigenvalue secondEigenfunction
  have hC : 0 < C := secondMoments.sharpConstant_pos
  let δ (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hδ (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  have hsmall (k : ℕ) : δ k ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    simp
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let L (k : ℕ) : ℝ≥0 := ⟨C * (1 - δ k), mul_nonneg hC.le (sub_nonneg.mpr (hsmall k))⟩
  have hL (k : ℕ) : (L k : ℝ≥0∞) < torsionTheory.G D := by
    rw [hG, ← ENNReal.ofReal_coe_nnreal]
    apply (ENNReal.ofReal_lt_ofReal_iff hC).mpr
    change C * (1 - δ k) < C
    nlinarith [mul_pos hC (hδ k)]
  choose p hp n hn R hsup hpos hconv hsub hout hflux using
    fun k => torsionTheory.exists_supporting_positive_radial_flux_gt D (hδ k) (hδ k) (hL k)
  let r (k : ℕ) := 2 * δ k + δ k
  have hr (k : ℕ) : 0 < r k := add_pos (mul_pos (by norm_num) (hδ k)) (hδ k)
  have hrlim : Tendsto r atTop (𝓝 0) := by simpa [r] using (hδlim.const_mul 2).add hδlim
  let F (k : ℕ) := D.gaugeOuterThickening (r k) (hr k)
  have hF : Tendsto (fun k => (F k).area) atTop (𝓝 1) := by
    rw [← hA]
    exact D.area_tendsto_of_outer_approximation F r hr hrlim
      (fun k => self_subset_thickening (hr k) _) (fun _ => Subset.rfl)
  have harea : Tendsto (fun k => radialArea (ContinuousProfiles.extend (R k))) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF
    · intro k
      change 1 ≤ radialArea (ContinuousProfiles.extend (R k))
      rw [radialArea_eq_volumeReal _ (hpos k), ← hA,
        ← D.inNormalFrame_area (p k) (n k) (hn k)]
      exact ENNReal.toReal_mono (ContinuousProfiles.domain_isMarked (hpos k)).2.1.measure_lt_top.ne
        (measure_mono (hsub k))
    · intro k
      change radialArea (ContinuousProfiles.extend (R k)) ≤ (F k).area
      rw [radialArea_eq_volumeReal _ (hpos k), ← (F k).inNormalFrame_area (p k) (n k) (hn k)]
      exact ENNReal.toReal_mono ((F k).inNormalFrame (p k) (n k) (hn k)).bounded.measure_lt_top.ne
        (measure_mono ((hout k).trans (thickening_frame_subset D (p k) (n k) (hn k) (r k) (hr k))))
  exact ⟨p, n, hn, fun k => radialDomain (ContinuousProfiles.extend (R k)), hp, hsub,
    radial_observation_excess_tendsto R hpos δ hδlim harea (fun k => (hflux k).le)⟩

end Torsion.Spectral

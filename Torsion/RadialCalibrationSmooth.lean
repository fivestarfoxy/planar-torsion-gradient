import Torsion.RadialCalibrationCutoff
import Torsion.SmoothCompactApproximation

/-!
# Radial calibration from smooth localized shape derivatives

Smooth compact perturbations are uniformly dense in continuous perturbations
that vanish near the endpoints. The actual dilation sandwich passes their
torsion fluxes to the limit; dominated convergence passes their calibration
integrals. The concrete endpoint exhaustion then covers every positive
continuous competitor. Only the localized Hadamard derivative itself remains
an explicit mathematical premise.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion.RadialCalibration

/-- Extend a supporting inequality from smooth compact perturbations to
continuous endpoint-preserving perturbations, over the actual weak flux. -/
theorem compact_calibration_of_smooth_perturbations {R₀ S γ : ℝ → ℝ}
    (h₀ : R₀ ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hS : S ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hγ : ContinuousOn γ (Icc 0 Real.pi))
    (hnear : ∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ Icc 0 Real.pi,
      (θ ≤ ε ∨ Real.pi - ε ≤ θ) → S θ = R₀ θ)
    (hsmooth : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo 0 Real.pi →
      (fun θ => R₀ θ + f θ) ∈ RadialFluxConcavity.positiveContinuousProfiles →
      torsionFlux (radialDomain (fun θ => R₀ θ + f θ)) ≤
        ∫ θ in Ioo 0 Real.pi, γ θ * (R₀ θ + f θ)) :
    torsionFlux (radialDomain S) ≤ ∫ θ in Ioo 0 Real.pi, γ θ * S θ := by
  obtain ⟨θ₀, hθ₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) Real.pi).Nonempty from ⟨0, le_rfl, Real.pi_pos.le⟩) hS.1
  let m := S θ₀
  have hm : 0 < m := hS.2 θ₀ hθ₀
  let ε : ℕ → ℝ := fun n => (m / 2) * (1 / ((n : ℝ) + 1))
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεm (n : ℕ) : ε n ≤ m / 2 := by
    have hinv : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).2 (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    simpa [ε] using mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ m / 2)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hi : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [ε] using hi.const_mul (m / 2)
  choose g hgs hgc hgu hga using fun n =>
    exists_smooth_compact_endpoint_approximation h₀.1 hS.1 hnear (hε n)
  let T : ℕ → ℝ → ℝ := fun n θ => R₀ θ + g n θ
  have herr (n : ℕ) (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) :
      |T n θ - S θ| < ε n := by
    have h := hga n θ hθ
    rw [Real.dist_eq] at h
    convert h using 1
    dsimp [T]
    congr 1
    ring
  have hT (n : ℕ) : T n ∈ RadialFluxConcavity.positiveContinuousProfiles := by
    refine ⟨h₀.1.add (hgs n).continuous.continuousOn, ?_⟩
    intro θ hθ
    have hb := (abs_lt.mp (herr n θ hθ)).1
    have hminimum : m ≤ S θ := hmin hθ
    have hsmall := hεm n
    nlinarith
  have huni : TendstoUniformlyOn T S atTop (Icc 0 Real.pi) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro δ hδ
    filter_upwards [hεlim.eventually (gt_mem_nhds hδ)] with n hn θ hθ
    have h := (herr n θ hθ).trans hn
    simpa [Real.dist_eq, abs_sub_comm] using h
  have hflux := torsionFlux_tendsto_of_uniform_radial hS hT huni
  have hint : Tendsto (fun n => ∫ θ in Ioo 0 Real.pi, γ θ * T n θ) atTop
      (𝓝 (∫ θ in Ioo 0 Real.pi, γ θ * S θ)) := by
    have hb : IntegrableOn (fun θ => |γ θ| * (|S θ| + m)) (Ioo 0 Real.pi) :=
      ((hγ.abs.mul (hS.1.abs.add continuousOn_const)).integrableOn_Icc).mono_set
        Ioo_subset_Icc_self
    apply tendsto_integral_of_dominated_convergence (fun θ => |γ θ| * (|S θ| + m))
      (fun n => ((hγ.mul (hT n).1).mono Ioo_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioo) hb
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have he : |T n θ - S θ| ≤ m :=
        (herr n θ ⟨hθ.1.le, hθ.2.le⟩).le.trans ((hεm n).trans (by linarith))
      have ha := abs_add_le (T n θ - S θ) (S θ)
      rw [sub_add_cancel] at ha
      linarith
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact tendsto_const_nhds.mul (huni.tendsto_at ⟨hθ.1.le, hθ.2.le⟩)
  exact le_of_tendsto_of_tendsto' hflux hint fun n =>
    hsmooth (g n) (hgs n) (hgc n) (hgu n) (hT n)

/-- Source-compatible radial calibration: the derivative premise is only
for smooth perturbations compactly supported in the open angular interval.
Uniform approximation and every endpoint limit are proved, not hypotheses. -/
theorem calibration_of_smooth_local_derivative {R₀ R γ : ℝ → ℝ}
    (h₀ : R₀ ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hR : R ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hγ : ContinuousOn γ (Icc 0 Real.pi))
    (heuler : torsionFlux (radialDomain R₀) = ∫ θ in Ioo 0 Real.pi, γ θ * R₀ θ)
    (hlocal : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo 0 Real.pi →
      (fun θ => R₀ θ + f θ) ∈ RadialFluxConcavity.positiveContinuousProfiles →
      HasDerivWithinAt (fun t : ℝ => torsionFlux
        (radialDomain (fun θ => R₀ θ + t * f θ)))
        (∫ θ in Ioo 0 Real.pi, γ θ * f θ) (Ioi 0) 0) :
    torsionFlux (radialDomain R) ≤ ∫ θ in Ioo 0 Real.pi, γ θ * R θ := by
  apply calibration_of_compact_perturbations h₀ hR hγ
  intro S hS hnear
  apply compact_calibration_of_smooth_perturbations h₀ hS hγ hnear
  intro f hfs hfc hfu hfpos
  have hpath : (fun t : ℝ => torsionFlux
      (radialDomain (AffineMap.lineMap R₀ (fun θ => R₀ θ + f θ) t))) =
      (fun t : ℝ => torsionFlux (radialDomain (fun θ => R₀ θ + t * f θ))) := by
    funext t
    apply congrArg torsionFlux
    apply congrArg radialDomain
    funext θ
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hd : HasDerivWithinAt (fun t : ℝ => torsionFlux
      (radialDomain (AffineMap.lineMap R₀ (fun θ => R₀ θ + f θ) t)))
      (∫ θ in Ioo 0 Real.pi, γ θ * f θ) (Ioi 0) 0 := by
    rw [hpath]
    exact hlocal f hfs hfc hfu hfpos
  have ht := Calibration.tangent_bound torsionFlux_radial_concaveOn h₀ hfpos hd
  have hi₀ : IntegrableOn (fun θ => γ θ * R₀ θ) (Ioo 0 Real.pi) :=
    ((hγ.mul h₀.1).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hif : IntegrableOn (fun θ => γ θ * f θ) (Ioo 0 Real.pi) :=
    ((hγ.mul hfs.continuous.continuousOn).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hi : (∫ θ in Ioo 0 Real.pi, γ θ * (R₀ θ + f θ)) =
      (∫ θ in Ioo 0 Real.pi, γ θ * R₀ θ) + ∫ θ in Ioo 0 Real.pi, γ θ * f θ := by
    simp_rw [mul_add]
    exact integral_add hi₀ hif
  rwa [heuler, ← hi] at ht

end Torsion.RadialCalibration

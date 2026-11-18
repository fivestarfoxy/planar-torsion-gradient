module

public import Torsion.Proof.PaperRadialHermite
public import Torsion.Proof.PaperBoundarySlopeMaximum

@[expose] public section

/-! # Orientation of the torsion gradient at a regular polar boundary -/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Torsion

/-- A vector perpendicular to a regular tangent points along its positive
quarter-turn if the two have the same sign on an inward direction. -/
private theorem oriented_normal (g v r : Plane) (hv : v ≠ 0)
    (ht : inner ℝ g v = 0) (hg : 0 ≤ inner ℝ g r)
    (hr : 0 < inner ℝ (Complex.I*v) r) :
    inner ℝ g (frameInwardNormal v) = ‖g‖ := by
  have hsq : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
  have hbase : ‖v‖ ^ 2 • g =
      inner ℝ g v • v + inner ℝ g (Complex.I*v) • (Complex.I*v) := by
    apply Complex.ext <;>
      simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.inner, Complex.real_smul,
        Complex.mul_re, Complex.mul_im] <;> ring
  rw [ht, zero_smul, zero_add] at hbase
  let k := (‖v‖ ^ 2)⁻¹ * inner ℝ g (Complex.I*v)
  have hgk : g = k • (Complex.I*v) := by
    calc
      g = (‖v‖^2)⁻¹ • (‖v‖^2 • g) := by rw [smul_smul, inv_mul_cancel₀ hsq, one_smul]
      _ = _ := by rw [hbase, smul_smul]
  have hk : 0 ≤ k := by
    rwa [hgk, real_inner_smul_left, mul_nonneg_iff_of_pos_right hr] at hg
  conv_lhs => rw [hgk]
  conv_rhs => rw [hgk]
  rw [frameInwardNormal, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_of_nonneg hk]
  simp only [norm_mul, Complex.norm_I, one_mul]
  field_simp [norm_ne_zero_iff.mpr hv]

/-- For nonnegative zero-Dirichlet data, a smooth boundary gradient is the
inward, positively oriented normal derivative. The result includes both
parameters at the seam by continuity. -/
theorem radialFrame_inwardSlope_eq_norm_gradient (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ))
    {u : Plane → ℝ} {N : Set Plane} (hN : IsOpen N) (hcl : closure D.carrier ⊆ N)
    (hu : ContDiffOn ℝ 1 u N) (hz : ∀ z ∈ frontier D.carrier, u z = 0)
    (hu0 : ∀ z ∈ D.carrier, 0 ≤ u z) :
    ∀ θ ∈ Icc (-Real.pi) Real.pi,
      frameInwardSlope u (radialFrameCurve c R θ) (deriv (radialFrameCurve c R) θ) =
        ‖gradient u (radialFrameCurve c R θ)‖ := by
  let γ := radialFrameCurve c R
  have hγ : ContDiff ℝ 1 γ := radialFrameCurve_contDiff c hR
  have hfront := radialFrameCurve_mem_frontier D c R hR hpos hmem
  have hγN : MapsTo γ (Icc (-Real.pi) Real.pi) N := fun _ h => hcl (frontier_subset_closure (hfront h))
  have hgrad := (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
    (hu.continuousOn_fderiv_of_isOpen hN (by simp))
  have hgradγ : ContinuousOn (fun θ => gradient u (γ θ)) (Icc (-Real.pi) Real.pi) :=
    hgrad.comp hγ.continuous.continuousOn hγN
  have hvγ := hγ.continuous_deriv (by simp)
  have hnormγ : Continuous (fun θ => frameInwardNormal (deriv γ θ)) :=
    (hvγ.norm.inv₀ (fun θ => (radialFrameCurve_speed_pos c hR hpos θ).ne')).smul
      (continuous_const.mul hvγ)
  have hopen : EqOn (fun θ => frameInwardSlope u (γ θ) (deriv γ θ))
      (fun θ => ‖gradient u (γ θ)‖) (Ioo (-Real.pi) Real.pi) := by
    intro θ hθ
    let z := γ θ
    let v := deriv γ θ
    have hc : z ∈ N := hγN (Ioo_subset_Icc_self hθ)
    have hdu := ((hu.differentiableOn (by simp)) z hc).differentiableAt (hN.mem_nhds hc)
    have huv : u z = 0 := hz z (hfront (Ioo_subset_Icc_self hθ))
    have ht : inner ℝ (gradient u z) v = 0 := by
      have hchain := hdu.hasFDerivAt.comp_hasDerivAt θ ((hγ.differentiable (by simp)) θ).hasDerivAt
      have heq : u ∘ γ =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy using
          hz (γ y) (hfront (Ioo_subset_Icc_self hy))
      have h := hchain.unique ((hasDerivAt_const θ (0:ℝ)).congr_of_eventuallyEq heq)
      simpa only [← fderiv_apply_eq_inner_gradient] using h
    have hgu : 0 ≤ inner ℝ (gradient u z) (c-z) := by
      have hr : HasDerivAt (fun s : ℝ => z + s • (c-z)) (c-z) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const (c-z)).const_add z
      have hd : HasFDerivAt u (fderiv ℝ u z) (z + (0:ℝ) • (c-z)) := by simpa using hdu.hasFDerivAt
      have hq := (hd.comp_hasDerivAt 0 hr).tendsto_slope_zero_right
      have he : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 ≤ u (z + t • (c-z)) / t := by
        filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
        have ht0 : 0 < t := ht
        have hrad : 0 < (1-t) * R θ := mul_pos (sub_pos.mpr ht1) (hpos θ)
        have hm := (hmem θ hθ _ hrad).mpr (by nlinarith [mul_pos ht0 (hpos θ)])
        have he : z + t • (c-z) = c + circleMap 0 ((1-t)*R θ) θ := by
          simp [z, γ, radialFrameCurve, circleMap, Complex.real_smul]
          ring
        exact div_nonneg (he ▸ hu0 _ hm) ht0.le
      have hlimit : Tendsto (fun t : ℝ => u (z + t • (c-z)) / t) (𝓝[>] 0) (𝓝 (inner ℝ (gradient u z) (c-z))) := by
        simpa only [Function.comp_apply, zero_add, zero_smul, add_zero, huv, sub_zero, smul_eq_mul,
          div_eq_mul_inv, mul_comm, fderiv_apply_eq_inner_gradient] using hq
      exact ge_of_tendsto hlimit he
    have hrd : 0 < inner ℝ (Complex.I*v) (c-z) := by
      have heq : inner ℝ (Complex.I*v) (c-z) = planarCross (z-c) v := by
        simp [Complex.inner, Complex.mul_re, Complex.mul_im, planarCross]; ring
      rw [heq, radialFrameCurve_cross c hR θ]
      exact sq_pos_of_pos (hpos θ)
    exact oriented_normal _ _ _ (norm_pos_iff.mp (radialFrameCurve_speed_pos c hR hpos θ)) ht hgu hrd
  have hclosure : closure (Ioo (-Real.pi) Real.pi) = Icc (-Real.pi) Real.pi := closure_Ioo (by linarith [Real.pi_pos])
  exact hopen.of_subset_closure (hgradγ.inner hnormγ.continuousOn) hgradγ.norm Ioo_subset_Icc_self hclosure.ge

/-- The true continuous extension of the weak torsion has nonnegative inward
slope, equal to the full gradient magnitude, along this entire frame. -/
theorem DirichletTheory.radialFrame_inwardSlope_eq_norm_gradient (T : DirichletTheory)
    (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ))
    {u : Plane → ℝ} {N : Set Plane} (hN : IsOpen N) (hcl : closure D.carrier ⊆ N)
    (hu : ContDiffOn ℝ 1 u N)
    (hrep : (T.solution D).value =ᵐ[volume.restrict D.carrier] u) :
    ∀ θ ∈ Icc (-Real.pi) Real.pi,
      frameInwardSlope u (radialFrameCurve c R θ) (deriv (radialFrameCurve c R) θ) =
        ‖gradient u (radialFrameCurve c R θ)‖ := by
  obtain ⟨s⟩ := T.exists_maximizingNormalSequence D
  have hsmall : D.carrier ⊆ N := subset_closure.trans hcl
  have heq : EqOn s.value u D.carrier := Measure.eqOn_open_of_ae_eq
    (s.value_eq.symm.trans hrep) D.isOpen s.continuous.continuousOn (hu.continuousOn.mono hsmall)
  have hclose := heq.of_subset_closure s.continuous.continuousOn
    (hu.continuousOn.mono hcl) subset_closure Subset.rfl
  apply Torsion.radialFrame_inwardSlope_eq_norm_gradient D c R hR hpos hmem hN hcl hu
  · intro z hz
    rw [← hclose (frontier_subset_closure hz)]
    exact s.zero_off _ (D.isOpen.frontier_eq ▸ hz).2
  · intro z hz
    rw [← heq hz]
    exact s.nonneg _

/-- A unit maximizing normal agrees with the frame normal at a point with
nonzero gradient and maximal inward slope. -/
theorem frameInwardNormal_eq_maximizing_normal {u : Plane → ℝ} {p v n : Plane}
    (hv : v ≠ 0) (hn : ‖n‖ = 1) (hp : 0 < ‖gradient u p‖)
    (hq : frameInwardSlope u p v = ‖gradient u p‖)
    (hmax : fderiv ℝ u p n = ‖gradient u p‖) : frameInwardNormal v = n := by
  let g := gradient u p
  have hvn : ‖frameInwardNormal v‖ = 1 := by simp [frameInwardNormal, norm_ne_zero_iff.mpr hv]
  have hg₁ : g = ‖g‖ • frameInwardNormal v := by
    have h : inner ℝ g (frameInwardNormal v) = ‖g‖ * ‖frameInwardNormal v‖ := by simpa only [hvn, mul_one, frameInwardSlope, g] using hq
    simpa only [hvn, one_smul] using inner_eq_norm_mul_iff_real.mp h
  have hg₂ : g = ‖g‖ • n := by
    have h : inner ℝ g n = ‖g‖ * ‖n‖ := by
      simpa only [hn, mul_one, fderiv_apply_eq_inner_gradient] using hmax
    simpa only [hn, one_smul] using inner_eq_norm_mul_iff_real.mp h
  exact (smul_right_injective _ hp.ne') (hg₁.symm.trans hg₂)

end Torsion

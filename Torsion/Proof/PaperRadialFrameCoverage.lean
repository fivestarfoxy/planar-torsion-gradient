module

public import Torsion.Proof.PaperRadialHermite

@[expose] public section

/-! # The radial parametrization reaches every boundary point -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion

private theorem unique_radial_frontier (D : ConvexDomain) {c v : Plane} (hc : c ∈ D.carrier)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : c + a • v ∈ frontier D.carrier) (hB : c + b • v ∈ frontier D.carrier) : a = b := by
  have hnot {a b : ℝ} (ha : 0 < a) (hab : a < b)
      (hA : c + a • v ∈ frontier D.carrier) (hB : c + b • v ∈ frontier D.carrier) : False := by
    let t := a / b
    have hb := ha.trans hab
    have ht : 0 < t := div_pos ha hb
    have ht1 : t < 1 := (div_lt_one hb).mpr hab
    have heq : (1 - t) • c + t • (c + b • v) = c + a • v := by
      rw [sub_smul, one_smul, smul_add, smul_smul, show t * b = a from div_mul_cancel₀ a hb.ne']
      abel
    have hseg : c + a • v ∈ openSegment ℝ c (c + b • v) := ⟨1 - t, t, sub_pos.mpr ht1, ht, by ring, heq⟩
    have hi := D.convex.openSegment_interior_closure_subset_interior (D.isOpen.interior_eq.symm ▸ hc)
      (frontier_subset_closure hB) hseg
    exact (D.isOpen.frontier_eq ▸ hA).2 (interior_subset hi)
  exact le_antisymm (le_of_not_gt fun h => hnot hb h hB hA) (le_of_not_gt fun h => hnot ha h hA hB)

/-- The radial membership law already makes the given center interior, by
convexity between two opposite small vertical radii. -/
theorem radialFrame_center_mem (D : ConvexDomain) (c : Plane) {R : ℝ → ℝ}
    (hpos : ∀ θ, 0 < R θ) (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ)) : c ∈ D.carrier := by
  let r := min (R (Real.pi / 2)) (R (-(Real.pi / 2))) / 2
  have hp := lt_min (hpos (Real.pi / 2)) (hpos (-(Real.pi / 2)))
  have hr : 0 < r := half_pos hp
  have h1 := (hmem (Real.pi / 2) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ r hr).mpr
    ((half_lt_self hp).trans_le (min_le_left _ _))
  have h2 := (hmem (-(Real.pi / 2)) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ r hr).mpr
    ((half_lt_self hp).trans_le (min_le_right _ _))
  have h := D.convex.midpoint_mem h1 h2
  have heq : midpoint ℝ (c + circleMap 0 r (Real.pi / 2)) (c + circleMap 0 r (-(Real.pi / 2))) = c := by
    simp only [midpoint_eq_smul_add, circleMap, zero_add, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_ofNat, ← neg_div, Complex.exp_neg_pi_div_two_mul_I, Complex.exp_pi_div_two_mul_I,
      Complex.real_smul]
    simp only [invOf_eq_inv, Complex.ofReal_inv, Complex.ofReal_ofNat]
    ring
  rwa [heq] at h

/-- The image of the closed parameter interval is the complete physical
frontier; the seam at angles ±π is included. -/
theorem radialFrameCurve_image_eq_frontier (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ)) :
    radialFrameCurve c R '' Icc (-Real.pi) Real.pi = frontier D.carrier := by
  have hfront := radialFrameCurve_mem_frontier D c R hR hpos hmem
  refine subset_antisymm hfront.image_subset ?_
  intro p hp
  have hc := radialFrame_center_mem D c hpos hmem
  have hne : p - c ≠ 0 := sub_ne_zero.mpr (fun h => (D.isOpen.frontier_eq ▸ hp).2 (h ▸ hc))
  let θ := (p - c).arg
  let v : Plane := Complex.exp ((θ : Plane) * Complex.I)
  have hθ : θ ∈ Icc (-Real.pi) Real.pi := ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hrad : c + ‖p - c‖ • v = p := by
    simp only [v, θ, Complex.real_smul, Complex.norm_mul_exp_arg_mul_I]
    abel
  have hg : radialFrameCurve c R θ = c + (R θ) • v := by simp [radialFrameCurve, circleMap, v, Complex.real_smul]
  have hRθ := unique_radial_frontier D hc (hpos θ) (norm_pos_iff.mpr hne) (hg ▸ hfront hθ) (hrad.symm ▸ hp)
  exact ⟨θ, hθ, by rwa [hg, hRθ]⟩

end Torsion

module

public import Torsion.Proof.PaperMaximizingFrame
public import Torsion.Proof.PaperExamplesWeak
public import Torsion.Proof.PaperExamplesEstimates
public import Mathlib.Analysis.InnerProductSpace.Convex

@[expose] public section

/-! # Strict convexity and the three-frame ranking -/

noncomputable section
open Set Metric
namespace Torsion
open Spectral

/-- A positive-radius flat segment at an attaining mark rules out equality for
any domain with strictly convex closure. -/
theorem G_lt_sharp_of_strictConvex_closure (D : ConvexDomain)
    (hsc : StrictConvex ℝ (closure D.carrier)) :
    torsionTheory.G D < ENNReal.ofReal
      (spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt D.area) := by
  apply lt_of_le_of_ne (torsionTheory.G_le_second_spectral_bound D)
  intro heq
  obtain ⟨_, p, n, _, _, _, _, hp, _, _, _, _, ht, _, hr, hpatch⟩ :=
    second_exists_maximizing_normal_flat_patch D heq
  let r := (torsionTheory.G D).toReal / Real.pi
  let v : Plane := r • (-Complex.I * n)
  have hv : v ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_smul, ht, mul_one, Real.norm_eq_abs, abs_of_pos hr]
    exact hr.ne'
  have hleft : p - v ∈ closure D.carrier := by
    have h := hpatch (-r) (by change abs (-r) ≤ r; rw [abs_neg, abs_of_pos (show 0 < r from hr)])
    simpa only [v, neg_smul, sub_eq_add_neg] using frontier_subset_closure h
  have hright : p + v ∈ closure D.carrier := frontier_subset_closure (hpatch r (le_of_eq (abs_of_pos hr)))
  have hne : p - v ≠ p + v := by
    intro h
    have hneg : -v = v := add_left_cancel (sub_eq_add_neg p v ▸ h)
    exact hv (neg_eq_self.mp hneg)
  have hin := hsc.openSegment_subset hleft hright hne (mem_openSegment_sub_add (𝕜 := ℝ) p v)
  rw [D.convex.interior_closure_eq_interior_of_nonempty_interior
    (by simpa only [D.isOpen.interior_eq] using D.nonempty), D.isOpen.interior_eq] at hin
  exact (D.isOpen.frontier_eq ▸ hp).2 hin

namespace PaperExamples

/-- A positive diagonal change of axes takes the closed disk to the closed ellipse. -/
theorem ellipse_strictConvex_closure {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    StrictConvex ℝ (closure (ellipse A B)) := by
  let e := ContinuousLinearEquiv.equivOfInverse (axes A B) (axes A⁻¹ B⁻¹)
    (fun z => by apply Complex.ext <;> simp [hA.ne', hB.ne'])
    (fun z => by apply Complex.ext <;> simp [hA.ne', hB.ne'])
  have hE : ellipse A B = e.toHomeomorph '' ball 0 1 := rfl
  rw [hE, ← e.toHomeomorph.image_closure, closure_ball (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)]
  exact (strictConvex_closedBall ℝ (0 : Plane) 1).linear_image e.toLinearMap e.toHomeomorph.isOpenMap

/-- The actual weak gradient on every ellipse lies strictly below the sharp
constant at that ellipse's area. -/
theorem ellipse_G_lt_sharp {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    torsionTheory.G (ellipseDomain hA hB) < ENNReal.ofReal
      (spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt (ellipseDomain hA hB).area) :=
  G_lt_sharp_of_strictConvex_closure _ (ellipse_strictConvex_closure hA hB)

/-- At equal area the disk has smaller peak slope than the optimal ellipse,
which in turn has smaller peak slope than the spectral optimizer. -/
theorem disk_best_ellipse_spectral_score_ranking :
    ellipseScore 1 < ellipseScore (Real.sqrt 3) ∧
      ellipseScore (Real.sqrt 3) < spectralConstant secondEigenvalue secondEigenfunction := by
  have hroot : 1 < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  refine ⟨(ellipseScore_optimal zero_lt_one).1.lt_of_ne (fun h =>
    (ne_of_lt hroot) ((ellipseScore_optimal zero_lt_one).2.mp h)), ?_⟩
  obtain ⟨B, hB, harea, hG⟩ := exists_area_one_ellipse_axes torsionTheory hroot.le
  have ha : 0 < Real.sqrt 3 * B := mul_pos (zero_lt_one.trans hroot) hB
  have he := ellipse_G_lt_sharp ha hB
  rw [hG, harea, Real.sqrt_one, mul_one] at he
  exact lt_of_not_ge fun h => (not_le_of_gt he) (ENNReal.ofReal_le_ofReal h)

/-- The exact three frame scores, including the two explicit physical constants. -/
theorem disk_best_ellipse_spectral_constants :
    1 / (2 * Real.sqrt Real.pi) < (3 : ℝ) ^ (3 / 4 : ℝ) / (4 * Real.sqrt Real.pi) ∧
      (3 : ℝ) ^ (3 / 4 : ℝ) / (4 * Real.sqrt Real.pi) <
        spectralConstant secondEigenvalue secondEigenfunction := by
  rw [← disk_score, ← best_ellipse_score_rpow]
  exact disk_best_ellipse_spectral_score_ranking

end PaperExamples
end Torsion

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The strict-curvature inequalities

This file checks the scalar inequalities used in Lemma 6.1. In the notation of
that lemma, `p` is the positive eigenfunction value, `dp` its derivative, and
`v` is the horizontal velocity. The determinant of the boundary tangent and
its derivative is `a * p ^ 2 - v * dp`.

The bounds on `v` and `dp` in the second case must be supplied separately from
the tangent inequality for the concave eigenfunction and the integral formula
for `v`. These theorems do not assert those analytic bounds.
-/

namespace Torsion
namespace Curvature

/-- The easy curvature case: the horizontal velocity and eigenfunction
slope have a nonpositive product. -/
theorem positive_of_nonpos_product {a p v dp : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hproduct : v * dp ≤ 0) :
    0 < a * p ^ 2 - v * dp := by
  have hmain : 0 < a * p ^ 2 := mul_pos ha (sq_pos_of_pos hp)
  linarith

/-- The difficult curvature case, reduced to the absolute-velocity estimate
and the strict tangent-line estimate. The conclusion also holds without
assuming the signs of `v` and `dp` agree. -/
theorem positive_of_tangent_bound {a p v dp d : ℝ}
    (ha : 0 < a) (hp : 0 < p)
    (hvelocity : |v| ≤ a * d * p)
    (htangent : d * |dp| < p) :
    0 < a * p ^ 2 - v * dp := by
  have hproduct : v * dp ≤ |v| * |dp| := by
    rw [← abs_mul]
    exact le_abs_self _
  have hbound : |v| * |dp| ≤ (a * d * p) * |dp| :=
    mul_le_mul_of_nonneg_right hvelocity (abs_nonneg _)
  have hstrict : (a * d * p) * |dp| < a * p ^ 2 := by
    calc
      _ = (a * p) * (d * |dp|) := by ring
      _ < (a * p) * p := mul_lt_mul_of_pos_left htangent (mul_pos ha hp)
      _ = a * p ^ 2 := by ring
  linarith

/-- Combining the two alternatives in the proof of Lemma 6.1. The distance
`d = |x - x₀|` is nonnegative; the algebraic theorem needs only its two bounds. -/
theorem positive_of_alternatives {a p v dp : ℝ}
    (ha : 0 < a) (hp : 0 < p)
    (hcases : v * dp ≤ 0 ∨
      ∃ d : ℝ, 0 ≤ d ∧ |v| ≤ a * d * p ∧ d * |dp| < p) :
    0 < a * p ^ 2 - v * dp := by
  rcases hcases with hproduct | ⟨d, _hd, hvelocity, htangent⟩
  · exact positive_of_nonpos_product ha hp hproduct
  · exact positive_of_tangent_bound ha hp hvelocity htangent

/-- At the top point the eigenfunction vanishes, while its derivative is
positive and the horizontal velocity is negative. -/
theorem positive_at_zero {v₀ dp₀ : ℝ}
    (hv₀ : v₀ < 0) (hdp₀ : 0 < dp₀) :
    0 < -v₀ * dp₀ :=
  mul_pos (neg_pos.mpr hv₀) hdp₀

/-- The curvature numerator at the top point, in the same formula used on
the rest of the arc. -/
theorem positive_at_zero_formula (a : ℝ) {v₀ dp₀ : ℝ}
    (hv₀ : v₀ < 0) (hdp₀ : 0 < dp₀) :
    0 < a * (0 : ℝ) ^ 2 - v₀ * dp₀ := by
  have h := positive_at_zero hv₀ hdp₀
  nlinarith

end Curvature
end Torsion

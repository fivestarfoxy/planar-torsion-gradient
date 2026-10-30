import Torsion.RestrictedSpectralOddGagliardo

/-!
# The exact positive-quadrant gap in odd absolute folding

The two paired kernels have different coefficients. Their exact
absolute-value gap is nonnegative on the positive quadrant and detects
opposite signs there. This includes the diagonal under total division.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- The actual gap between a positive-quadrant pair and its absolute fold. -/
def oddAbsGap (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  2 * (|f x * f y| - f x * f y) *
    (1 / (x - y) ^ 2 - 1 / (x + y) ^ 2)

/-- Exact scalar identity for the real paired kernel. -/
theorem oddGagliardoPair_abs_gap (f : ℝ → ℝ) (x y : ℝ) :
    oddGagliardoPair f x y = oddGagliardoPair (fun z => |f z|) x y + oddAbsGap f x y := by
  have hdiff : (f x - f y) ^ 2 = (|f x| - |f y|) ^ 2 +
      2 * (|f x * f y| - f x * f y) := by
    rw [abs_mul]
    nlinarith [sq_abs (f x), sq_abs (f y)]
  have hsum : (f x + f y) ^ 2 = (|f x| + |f y|) ^ 2 -
      2 * (|f x * f y| - f x * f y) := by
    rw [abs_mul]
    nlinarith [sq_abs (f x), sq_abs (f y)]
  unfold oddGagliardoPair oddAbsGap
  rw [hdiff, hsum]
  ring

/-- Off the diagonal, the same-half coefficient is strictly larger than
the reflected-half coefficient. -/
theorem oddAbsGap_coefficient_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    0 < 1 / (x - y) ^ 2 - 1 / (x + y) ^ 2 := by
  apply sub_pos.2
  exact one_div_lt_one_div_of_lt (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
    (by nlinarith [mul_pos hx hy])

/-- The exact gap is nonnegative throughout the positive quadrant,
including the diagonal where its sign-detecting factor vanishes. -/
theorem oddAbsGap_nonneg (f : ℝ → ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ oddAbsGap f x y := by
  by_cases hxy : x = y
  · subst y
    have hs : |f x * f x| = f x * f x := abs_of_nonneg (mul_self_nonneg _)
    simp [oddAbsGap, hs]
  · exact mul_nonneg (mul_nonneg (by norm_num)
      (sub_nonneg.2 (le_abs_self (f x * f y)))) (oddAbsGap_coefficient_pos hx hy hxy).le

/-- A nonpositive gap on the positive quadrant forces a nonnegative
product of the actual values; no continuity or nonzero point assumptions
are required. -/
theorem oddAbsGap_le_zero_imp_mul_nonneg (f : ℝ → ℝ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hle : oddAbsGap f x y ≤ 0) : 0 ≤ f x * f y := by
  by_cases hxy : x = y
  · subst y
    exact mul_self_nonneg _
  · by_contra! hprod
    have hfactor : 0 < |f x * f y| - f x * f y := by
      rw [abs_of_neg hprod]
      linarith
    have hpos : 0 < oddAbsGap f x y :=
      mul_pos (mul_pos (by norm_num) hfactor) (oddAbsGap_coefficient_pos hx hy hxy)
    exact (not_lt_of_ge hle) hpos

end Torsion.Spectral

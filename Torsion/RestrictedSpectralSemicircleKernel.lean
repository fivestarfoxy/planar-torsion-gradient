import Torsion.RestrictedSpectralGagliardoAdmission

/-! Elementary two-point endpoint estimates for the semicircle barrier. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

private def circle (x : ℝ) : ℝ := Real.sqrt (max (1 - x ^ 2) 0)
private def circleAbs (x : ℝ) : ℝ := Real.sqrt |1 - x ^ 2|

private theorem circle_eq_of_nonneg {x : ℝ} (hx : 0 ≤ 1 - x ^ 2) :
    circle x = circleAbs x := by simp [circle, circleAbs, max_eq_left hx, abs_of_nonneg hx]

private theorem circle_eq_zero_of_nonpos {x : ℝ} (hx : 1 - x ^ 2 ≤ 0) :
    circle x = 0 := by simp [circle, max_eq_right hx]

private theorem circleAbs_sq (x : ℝ) : circleAbs x ^ 2 = |1 - x ^ 2| :=
  Real.sq_sqrt (abs_nonneg _)

private theorem circleAbs_pos {x : ℝ} (hx : 1 - x ^ 2 ≠ 0) : 0 < circleAbs x :=
  Real.sqrt_pos.2 (abs_pos.2 hx)

/-- A bounded-square majorant separates the two square-root endpoint
singularities. The excluded endpoint lines have product measure zero. -/
theorem semicircleKernel_local_bound {x y : ℝ}
    (hx : |x| < 2) (hy : |y| < 2)
    (hxend : 1 - x ^ 2 ≠ 0) (hyend : 1 - y ^ 2 ≠ 0) :
    (Real.sqrt (max (1 - y ^ 2) 0) - Real.sqrt (max (1 - x ^ 2) 0)) ^ 2 /
      (y - x) ^ 2 ≤
      16 * (Real.sqrt |1 - x ^ 2|)⁻¹ * (Real.sqrt |1 - y ^ 2|)⁻¹ := by
  change (circle y - circle x) ^ 2 / (y - x) ^ 2 ≤
    16 * (circleAbs x)⁻¹ * (circleAbs y)⁻¹
  have hsx : 0 < circleAbs x := circleAbs_pos hxend
  have hsy : 0 < circleAbs y := circleAbs_pos hyend
  by_cases hxy : y = x
  · simp only [hxy, sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_div]
    positivity
  have hden : 0 < (y - x) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.2 hxy)
  have hroot : 0 < circleAbs x * circleAbs y := mul_pos hsx hsy
  rw [show 16 * (circleAbs x)⁻¹ * (circleAbs y)⁻¹ =
    16 / (circleAbs x * circleAbs y) by simp only [div_eq_mul_inv, mul_inv]; ring]
  apply (div_le_div_iff₀ hden hroot).2
  have hsum : (x + y) ^ 2 ≤ 16 := by
    have hx' := abs_lt.mp hx
    have hy' := abs_lt.mp hy
    nlinarith [sq_nonneg (x - y)]
  by_cases hxin : 0 ≤ 1 - x ^ 2
  · rw [circle_eq_of_nonneg hxin]
    by_cases hyin : 0 ≤ 1 - y ^ 2
    · rw [circle_eq_of_nonneg hyin]
      have hsx2 : circleAbs x ^ 2 = 1 - x ^ 2 := by rw [circleAbs_sq, abs_of_nonneg hxin]
      have hsy2 : circleAbs y ^ 2 = 1 - y ^ 2 := by rw [circleAbs_sq, abs_of_nonneg hyin]
      have hprod : circleAbs x * circleAbs y ≤ (circleAbs y + circleAbs x) ^ 2 := by nlinarith
      have heq : (circleAbs y - circleAbs x) ^ 2 * (circleAbs y + circleAbs x) ^ 2 =
          (y - x) ^ 2 * (x + y) ^ 2 := by
        calc
          _ = (circleAbs y ^ 2 - circleAbs x ^ 2) ^ 2 := by ring
          _ = _ := by rw [hsx2, hsy2]; ring
      calc
        _ ≤ (circleAbs y - circleAbs x) ^ 2 * (circleAbs y + circleAbs x) ^ 2 :=
          mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
        _ = (y - x) ^ 2 * (x + y) ^ 2 := heq
        _ ≤ 16 * (y - x) ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hsum hden.le]
    · rw [circle_eq_zero_of_nonpos (le_of_not_ge hyin), zero_sub, neg_sq]
      have hsx2 : circleAbs x ^ 2 = 1 - x ^ 2 := by rw [circleAbs_sq, abs_of_nonneg hxin]
      have hsy2 : circleAbs y ^ 2 = y ^ 2 - 1 := by rw [circleAbs_sq, abs_of_neg (lt_of_not_ge hyin)]; ring
      have hprod : circleAbs x * circleAbs y ≤ circleAbs x ^ 2 + circleAbs y ^ 2 := by nlinarith [sq_nonneg (circleAbs x - circleAbs y)]
      have h₁ := mul_le_mul_of_nonneg_left hprod (sq_nonneg (circleAbs x))
      have h₂ : circleAbs x ^ 2 * (circleAbs x ^ 2 + circleAbs y ^ 2) ≤
          (circleAbs x ^ 2 + circleAbs y ^ 2) ^ 2 := by
        nlinarith [sq_nonneg (circleAbs x * circleAbs y), sq_nonneg (circleAbs y ^ 2)]
      have heq : (circleAbs x ^ 2 + circleAbs y ^ 2) ^ 2 =
          (y - x) ^ 2 * (x + y) ^ 2 := by rw [hsx2, hsy2]; ring
      nlinarith [mul_le_mul_of_nonneg_left hsum hden.le]
  · rw [circle_eq_zero_of_nonpos (le_of_not_ge hxin), sub_zero]
    by_cases hyin : 0 ≤ 1 - y ^ 2
    · rw [circle_eq_of_nonneg hyin]
      have hsx2 : circleAbs x ^ 2 = x ^ 2 - 1 := by rw [circleAbs_sq, abs_of_neg (lt_of_not_ge hxin)]; ring
      have hsy2 : circleAbs y ^ 2 = 1 - y ^ 2 := by rw [circleAbs_sq, abs_of_nonneg hyin]
      have hprod : circleAbs x * circleAbs y ≤ circleAbs x ^ 2 + circleAbs y ^ 2 := by nlinarith [sq_nonneg (circleAbs x - circleAbs y)]
      have h₁ := mul_le_mul_of_nonneg_left hprod (sq_nonneg (circleAbs y))
      have h₂ : circleAbs y ^ 2 * (circleAbs x ^ 2 + circleAbs y ^ 2) ≤
          (circleAbs x ^ 2 + circleAbs y ^ 2) ^ 2 := by
        nlinarith [sq_nonneg (circleAbs x * circleAbs y), sq_nonneg (circleAbs x ^ 2)]
      have heq : (circleAbs x ^ 2 + circleAbs y ^ 2) ^ 2 =
          (y - x) ^ 2 * (x + y) ^ 2 := by rw [hsx2, hsy2]; ring
      nlinarith [mul_le_mul_of_nonneg_left hsum hden.le]
    · rw [circle_eq_zero_of_nonpos (le_of_not_ge hyin)]
      simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul]
      positivity

/-- The tail needs only the standard integrable rational decay. -/
theorem semicircleKernel_tail_bound {x y : ℝ}
    (hx : 1 - x ^ 2 ≠ 0) (hy : 2 ≤ |y|) :
    (Real.sqrt (max (1 - y ^ 2) 0) - Real.sqrt (max (1 - x ^ 2) 0)) ^ 2 /
      (y - x) ^ 2 ≤
      16 * (Real.sqrt |1 - x ^ 2|)⁻¹ * (1 + y ^ 2)⁻¹ := by
  have hy2 : 4 ≤ y ^ 2 := by nlinarith [sq_abs y]
  have hyout : 1 - y ^ 2 ≤ 0 := by linarith
  change (circle y - circle x) ^ 2 / (y - x) ^ 2 ≤
    16 * (circleAbs x)⁻¹ * (1 + y ^ 2)⁻¹
  rw [circle_eq_zero_of_nonpos hyout, zero_sub, neg_sq]
  by_cases hxout : 1 - x ^ 2 ≤ 0
  · rw [circle_eq_zero_of_nonpos hxout]
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div]
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 (Real.sqrt_nonneg _)))
      (inv_nonneg.2 (by positivity))
  have hxin : 0 < 1 - x ^ 2 := lt_of_not_ge hxout
  rw [circle_eq_of_nonneg hxin.le]
  have hsx : 0 < circleAbs x := circleAbs_pos hx
  have hsx2 : circleAbs x ^ 2 = 1 - x ^ 2 := by rw [circleAbs_sq, abs_of_pos hxin]
  have hsx1 : circleAbs x ≤ 1 := by nlinarith [sq_nonneg x]
  have hden : 0 < (y - x) ^ 2 := by nlinarith [sq_nonneg (y - 2 * x)]
  have hroot : 0 < circleAbs x * (1 + y ^ 2) := by positivity
  rw [show 16 * (circleAbs x)⁻¹ * (1 + y ^ 2)⁻¹ =
    16 / (circleAbs x * (1 + y ^ 2)) by simp only [div_eq_mul_inv, mul_inv]; ring]
  apply (div_le_div_iff₀ hden hroot).2
  have hb : circleAbs x ^ 2 * circleAbs x ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hsx1 (sq_nonneg (circleAbs x))]
  have hh := mul_le_mul_of_nonneg_right hb (show 0 ≤ 1 + y ^ 2 by positivity)
  nlinarith [sq_nonneg (y - 2 * x)]

end Torsion.Spectral

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! A quadratic modulus estimate for the ordinary real cosine. -/
namespace Torsion.Spectral

/-- The cosine changes by at most half the change of the squared argument.
This global estimate is useful when a mean-zero Fourier transform is
paired with a suitable constant cosine. -/
theorem abs_cos_sub_cos_le_half_abs_sq_sub_sq (u v : ℝ) :
    |Real.cos u - Real.cos v| ≤ |u ^ 2 - v ^ 2| / 2 := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul]
  have h := mul_le_mul (Real.abs_sin_le_abs (x := (u + v) / 2))
    (Real.abs_sin_le_abs (x := (u - v) / 2))
    (abs_nonneg (Real.sin ((u - v) / 2))) (abs_nonneg ((u + v) / 2))
  have htwo := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    |-2| * |Real.sin ((u + v) / 2)| * |Real.sin ((u - v) / 2)| =
        2 * (|Real.sin ((u + v) / 2)| * |Real.sin ((u - v) / 2)|) := by norm_num; ring
    _ ≤ 2 * (|(u + v) / 2| * |(u - v) / 2|) := htwo
    _ = |u ^ 2 - v ^ 2| / 2 := by
      rw [← abs_mul]
      have hsq : (u + v) / 2 * ((u - v) / 2) = (u ^ 2 - v ^ 2) / 4 := by ring
      rw [hsq, abs_div]
      norm_num
      ring

end Torsion.Spectral

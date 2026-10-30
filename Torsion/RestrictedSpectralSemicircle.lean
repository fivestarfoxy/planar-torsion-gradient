import Torsion.SpectralHolderCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The concrete semicircle barrier

This is the original zero-exterior square-root profile. Its form admission
and weak half-Laplacian equation are proved in separate modules.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion.Spectral

def semicircleBarrier (x : ℝ) : ℝ := Real.sqrt (max (1 - x ^ 2) 0)

theorem semicircleBarrier_nonneg (x : ℝ) : 0 ≤ semicircleBarrier x := Real.sqrt_nonneg _

theorem semicircleBarrier_sq (x : ℝ) :
    semicircleBarrier x ^ 2 = max (1 - x ^ 2) 0 :=
  Real.sq_sqrt (le_max_right _ _)

theorem semicircleBarrier_eq_sqrt (x : ℝ) :
    semicircleBarrier x = Real.sqrt (1 - x ^ 2) := by
  by_cases h : 0 ≤ 1 - x ^ 2
  · simp only [semicircleBarrier, max_eq_left h]
  · have hn : 1 - x ^ 2 ≤ 0 := le_of_not_ge h
    simp only [semicircleBarrier, max_eq_right hn, Real.sqrt_zero,
      Real.sqrt_eq_zero_of_nonpos hn]

theorem semicircleBarrier_continuous : Continuous semicircleBarrier :=
  Real.continuous_sqrt.comp ((continuous_const.sub (continuous_id.pow 2)).max continuous_const)

theorem semicircleBarrier_even : Function.Even semicircleBarrier := by
  intro x
  simp only [semicircleBarrier, neg_sq]

theorem semicircleBarrier_zero_exterior (x : ℝ) (hx : 1 ≤ |x|) :
    semicircleBarrier x = 0 := by
  have hs : 1 ≤ x ^ 2 := by nlinarith [sq_abs x]
  simp only [semicircleBarrier, max_eq_right (by linarith : 1 - x ^ 2 ≤ 0), Real.sqrt_zero]

theorem semicircleBarrier_sq_interior {x : ℝ} (hx : |x| < 1) :
    semicircleBarrier x ^ 2 = 1 - x ^ 2 := by
  rw [semicircleBarrier_sq, max_eq_left]
  have h := (sq_lt_one_iff_abs_lt_one x).2 hx
  linarith

theorem semicircleBarrier_pos {x : ℝ} (hx : |x| < 1) : 0 < semicircleBarrier x := by
  rw [semicircleBarrier_eq_sqrt, Real.sqrt_pos]
  have h := (sq_lt_one_iff_abs_lt_one x).2 hx
  linarith

theorem semicircleBarrier_le_one (x : ℝ) : semicircleBarrier x ≤ 1 := by
  have hs : semicircleBarrier x ^ 2 ≤ 1 := by
    rw [semicircleBarrier_sq]
    exact max_le (by nlinarith [sq_nonneg x]) (by norm_num)
  nlinarith [semicircleBarrier_nonneg x]

theorem semicircleBarrier_hasCompactSupport : HasCompactSupport semicircleBarrier := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-1 : ℝ) 1) isCompact_Icc
  intro x hx
  by_contra hn
  have ha : 1 ≤ |x| := le_of_not_ge fun h => hn (abs_le.1 h)
  exact hx (semicircleBarrier_zero_exterior x ha)

theorem semicircleBarrier_integrable : Integrable semicircleBarrier :=
  semicircleBarrier_continuous.integrable_of_hasCompactSupport semicircleBarrier_hasCompactSupport

theorem semicircleBarrier_memLp : MemLp semicircleBarrier 2 volume :=
  semicircleBarrier_continuous.memLp_of_hasCompactSupport semicircleBarrier_hasCompactSupport

theorem semicircleBarrier_contDiffOn :
    ContDiffOn ℝ ∞ semicircleBarrier (Ioo (-1 : ℝ) 1) := by
  have heq : semicircleBarrier = fun x : ℝ => Real.sqrt (1 - x ^ 2) :=
    funext semicircleBarrier_eq_sqrt
  rw [heq]
  apply (contDiff_const.sub (contDiff_id.pow 2)).contDiffOn.sqrt
  intro x hx
  have h : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 (abs_lt.2 hx)
  simp only [id_eq]
  linarith

private theorem semicircleBarrier_sq_clamped (x : ℝ) :
    semicircleBarrier x ^ 2 = 1 - (min |x| 1) ^ 2 := by
  by_cases hx : |x| ≤ 1
  · have hs : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
    rw [semicircleBarrier_sq, min_eq_left hx,
      max_eq_left (by linarith : 0 ≤ 1 - x ^ 2), sq_abs]
  · have ha : 1 ≤ |x| := le_of_not_ge hx
    rw [semicircleBarrier_zero_exterior x ha, min_eq_right ha]
    norm_num

private theorem square_root_gap_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2| := by
  rcases le_total a b with h | h
  · have hs : a ^ 2 - b ^ 2 ≤ 0 := by nlinarith
    rw [abs_of_nonpos hs]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr h)]
  · have hs : 0 ≤ a ^ 2 - b ^ 2 := by nlinarith
    rw [abs_of_nonneg hs]
    nlinarith [mul_nonneg hb (sub_nonneg.mpr h)]

/-- An elementary global square-root modulus, including exterior points. -/
theorem semicircleBarrier_sub_sq_le (x y : ℝ) :
    (semicircleBarrier x - semicircleBarrier y) ^ 2 ≤ 2 * |x - y| := by
  have habs : LipschitzWith 1 (fun x : ℝ => |x|) := by
    apply LipschitzWith.mk_one
    intro x y
    simpa only [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y
  have hclip := (habs.min_const 1).dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hclip
  have hcx : 0 ≤ min |x| (1 : ℝ) := le_min (abs_nonneg _) (by norm_num)
  have hcy : 0 ≤ min |y| (1 : ℝ) := le_min (abs_nonneg _) (by norm_num)
  have hsum : min |x| (1 : ℝ) + min |y| 1 ≤ 2 := by
    linarith [min_le_right |x| (1 : ℝ), min_le_right |y| (1 : ℝ)]
  have heq : semicircleBarrier x ^ 2 - semicircleBarrier y ^ 2 =
      (min |x| 1 - min |y| 1) * (-(min |x| 1 + min |y| 1)) := by
    rw [semicircleBarrier_sq_clamped, semicircleBarrier_sq_clamped]
    ring
  have hquad : |semicircleBarrier x ^ 2 - semicircleBarrier y ^ 2| ≤ 2 * |x - y| := by
    rw [heq, abs_mul, abs_neg, abs_of_nonneg (add_nonneg hcx hcy)]
    have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg (min |x| 1 - min |y| 1))
    nlinarith
  exact (square_root_gap_le (semicircleBarrier_nonneg x) (semicircleBarrier_nonneg y)).trans hquad

theorem semicircleBarrier_holder_half : HolderWith 2 (1 / 2) semicircleBarrier := by
  apply holderWith_of_dist_bound
  intro x y
  norm_num only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one]
  rw [Real.dist_eq, Real.dist_eq, ← Real.sqrt_eq_rpow]
  have h := semicircleBarrier_sub_sq_le x y
  have hs := Real.sq_sqrt (abs_nonneg (x - y))
  have ha := sq_abs (semicircleBarrier x - semicircleBarrier y)
  have hnonneg := Real.sqrt_nonneg |x - y|
  nlinarith [abs_nonneg (semicircleBarrier x - semicircleBarrier y)]

end Torsion.Spectral

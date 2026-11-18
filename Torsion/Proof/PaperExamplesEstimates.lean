module

public import Torsion.Proof.PaperExamples
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! # Certified decimal comparisons in Section 7

These intervals justify the two rounded benchmarks using rational arithmetic
and the bounds for π in mathlib. -/

namespace Torsion.PaperExamples

theorem ellipseScore_rpow {r : ℝ} (hr : 0 < r) :
    ellipseScore r = r ^ (3 / 2 : ℝ) / (Real.sqrt Real.pi * (1 + r ^ 2)) := by
  unfold ellipseScore
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hr, Real.rpow_one,
    ← Real.sqrt_eq_rpow, mul_comm (1 + r ^ 2)]

theorem best_ellipse_score_rpow : ellipseScore (Real.sqrt 3) =
    (3 : ℝ) ^ (3 / 4 : ℝ) / (4 * Real.sqrt Real.pi) := by
  rw [best_ellipse_score, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add (by norm_num)]
  norm_num

private theorem sqrt_pi_bounds :
    1.7724538509055 < Real.sqrt Real.pi ∧ Real.sqrt Real.pi < 1.7724538509056 := by
  constructor
  · apply (Real.lt_sqrt (by norm_num)).2
    linarith [Real.pi_gt_d20]
  · apply (Real.sqrt_lt' (by norm_num)).2
    linarith [Real.pi_lt_d20]

/-- `0.2820947918` rounded to ten decimal places. -/
theorem disk_score_decimal : 0.28209479175 < ellipseScore 1 ∧
    ellipseScore 1 < 0.28209479185 := by
  have hd : 0 < 2 * Real.sqrt Real.pi := by positivity
  rw [disk_score, lt_div_iff₀ hd, div_lt_iff₀ hd]
  constructor <;> linarith [sqrt_pi_bounds.1, sqrt_pi_bounds.2]

/-- `0.3215185343` rounded to ten decimal places. -/
theorem best_ellipse_score_decimal :
    0.32151853425 < ellipseScore (Real.sqrt 3) ∧
      ellipseScore (Real.sqrt 3) < 0.32151853435 := by
  have hs₁ : 1.7320508075688 < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs₂ : Real.sqrt 3 < 1.7320508075689 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have ht₁ : 1.3160740129524 < Real.sqrt (Real.sqrt 3) := by
    apply (Real.lt_sqrt (by norm_num)).2
    linarith
  have ht₂ : Real.sqrt (Real.sqrt 3) < 1.3160740129526 := by
    apply (Real.sqrt_lt' (by norm_num)).2
    linarith
  have hl : (1.7320508075688 : ℝ) * 1.3160740129524 <
      Real.sqrt 3 * Real.sqrt (Real.sqrt 3) := by gcongr
  have hu : Real.sqrt 3 * Real.sqrt (Real.sqrt 3) <
      (1.7320508075689 : ℝ) * 1.3160740129526 := by gcongr
  have hd : 0 < 4 * Real.sqrt Real.pi := by positivity
  rw [best_ellipse_score, lt_div_iff₀ hd, div_lt_iff₀ hd]
  constructor <;> linarith [sqrt_pi_bounds.1, sqrt_pi_bounds.2]

end Torsion.PaperExamples

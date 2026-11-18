module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # The disk and optimal ellipse in Section 7

The ellipse has semiaxes `A ≥ B > 0`. Its peak boundary slope divided by the
square root of its area depends only on the aspect ratio. The equality proof
below factors the deficit, so also proves uniqueness. -/

noncomputable section
open Filter
open scoped Topology

namespace Torsion.PaperExamples

/-- Area-normalized peak gradient for an ellipse of aspect ratio `r`. -/
def ellipseScore (r : ℝ) : ℝ :=
  r * Real.sqrt r / ((1 + r ^ 2) * Real.sqrt Real.pi)

/-- Short-axis gradient of the quadratic torsion field. -/
def shortAxisSlope (A B : ℝ) : ℝ := A ^ 2 * B / (A ^ 2 + B ^ 2)

/-- Substituting `A = r B` into the peak gradient and the area `πAB`. -/
theorem normalize_shortAxisSlope {r B : ℝ} (hr : 0 < r) (hB : 0 < B) :
    shortAxisSlope (r * B) B / Real.sqrt (Real.pi * (r * B) * B) = ellipseScore r := by
  have harea : Real.pi * (r * B) * B = (Real.pi * r) * B ^ 2 := by ring
  rw [harea, Real.sqrt_mul (mul_nonneg Real.pi_pos.le hr.le),
    Real.sqrt_sq hB.le, Real.sqrt_mul Real.pi_pos.le]
  unfold shortAxisSlope ellipseScore
  have hs := Real.sq_sqrt hr.le
  have hsr := Real.sqrt_pos.2 hr
  have hsp := Real.sqrt_pos.2 Real.pi_pos
  field_simp
  nlinarith [hs]

theorem disk_score : ellipseScore 1 = 1 / (2 * Real.sqrt Real.pi) := by
  norm_num [ellipseScore]

/-- The logarithmic derivative from Section 7. -/
theorem log_ellipseScore_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Real.log (ellipseScore s))
      ((3 - r ^ 2) / (2 * r * (1 + r ^ 2))) r := by
  have hsr := Real.sqrt_pos.2 hr
  have hsp := Real.sqrt_pos.2 Real.pi_pos
  have hden : 0 < (1 + r ^ 2) * Real.sqrt Real.pi := by positivity
  have hval : 0 < ellipseScore r := by unfold ellipseScore; positivity
  have hd := (((hasDerivAt_id r).mul (Real.hasDerivAt_sqrt hr.ne')).div
    (((hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).pow 2)).mul_const
      (Real.sqrt Real.pi)) hden.ne').log hval.ne'
  convert hd using 1 <;> try rfl
  dsimp
  have hs := Real.sq_sqrt hr.le
  generalize Real.sqrt r = t at hs hsr ⊢
  rw [← hs]
  field_simp
  ring

/-- Young's sharp monomial inequality in the form needed for this aspect ratio. -/
private theorem quartic_deficit {x y : ℝ} (hy : y ^ 4 = 3) :
    3 + 3 * x ^ 4 - 4 * x ^ 3 * y =
      (x - y) ^ 2 * ((x + y) ^ 2 + 2 * x ^ 2) := by
  linear_combination -hy

/-- `√3` is the unique optimizing aspect ratio. -/
theorem ellipseScore_optimal {r : ℝ} (hr : 0 < r) :
    ellipseScore r ≤ ellipseScore (Real.sqrt 3) ∧
      (ellipseScore r = ellipseScore (Real.sqrt 3) ↔ r = Real.sqrt 3) := by
  let x := Real.sqrt r
  let y := Real.sqrt (Real.sqrt 3)
  have hx : 0 < x := Real.sqrt_pos.2 hr
  have hy : 0 < y := by dsimp [y]; positivity
  have hx2 : x ^ 2 = r := Real.sq_sqrt hr.le
  have hy2 : y ^ 2 = Real.sqrt 3 := Real.sq_sqrt (by positivity)
  have hy4 : y ^ 4 = 3 := by
    calc y ^ 4 = (y ^ 2) ^ 2 := by ring
         _ = 3 := by rw [hy2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hp : 0 < (x + y) ^ 2 + 2 * x ^ 2 := by positivity
  have hq := quartic_deficit (x := x) hy4
  have bound : x ^ 3 * (1 + y ^ 4) ≤ y ^ 3 * (1 + x ^ 4) := by
    apply (mul_le_mul_iff_left₀ hy).mp
    nlinarith [sq_nonneg (x-y), mul_nonneg (sq_nonneg (x-y)) hp.le,
      congrArg (fun t : ℝ => t * x ^ 4) hy4, congrArg (fun t : ℝ => t * x ^ 3 * y) hy4]
  have score_r : ellipseScore r = x ^ 3 / ((1 + x ^ 4) * Real.sqrt Real.pi) := by
    unfold ellipseScore
    change r * x / _ = _
    rw [← hx2]
    ring
  have score_s : ellipseScore (Real.sqrt 3) = y ^ 3 / ((1 + y ^ 4) * Real.sqrt Real.pi) := by
    unfold ellipseScore
    change Real.sqrt 3 * y / _ = _
    rw [← hy2]
    ring
  rw [score_r, score_s]
  have dx : 0 < (1 + x ^ 4) * Real.sqrt Real.pi := by positivity
  have dy : 0 < (1 + y ^ 4) * Real.sqrt Real.pi := by positivity
  constructor
  · apply (div_le_div_iff₀ dx dy).2
    simpa only [← mul_assoc] using mul_le_mul_of_nonneg_right bound hπ.le
  · constructor
    · intro heq
      have hcross := (div_eq_div_iff dx.ne' dy.ne').mp heq
      have heq' : x ^ 3 * (1 + y ^ 4) = y ^ 3 * (1 + x ^ 4) := by
        apply mul_right_cancel₀ hπ.ne'
        simpa only [mul_assoc] using hcross
      have hz : (x - y) ^ 2 * ((x + y) ^ 2 + 2 * x ^ 2) = 0 := by
        rw [← hq]
        rw [hy4] at heq'
        nlinarith [congrArg (fun t : ℝ => y * t) heq',
          congrArg (fun t : ℝ => t * x ^ 4) hy4]
      have hxy : x = y := by
        have he := (mul_eq_zero.mp hz).resolve_right hp.ne'
        nlinarith [sq_nonneg (x-y)]
      simp only [← hx2, ← hy2, hxy]
    · intro he
      have hxy : x = y := by change Real.sqrt r = _; rw [he]
      rw [hxy]

theorem best_ellipse_score : ellipseScore (Real.sqrt 3) =
    Real.sqrt 3 * Real.sqrt (Real.sqrt 3) / (4 * Real.sqrt Real.pi) := by
  unfold ellipseScore
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- Elongation drives the normalized peak to zero. -/
theorem ellipseScore_tendsto_zero : Tendsto ellipseScore atTop (𝓝 0) := by
  have hlim : Tendsto (fun r : ℝ => (Real.sqrt r)⁻¹ * (Real.sqrt Real.pi)⁻¹)
      atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).mul_const
      (Real.sqrt Real.pi)⁻¹
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    unfold ellipseScore
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hs := Real.sqrt_pos.2 hr
    have hπ := Real.sqrt_pos.2 Real.pi_pos
    unfold ellipseScore
    field_simp
    nlinarith [congrArg (fun t : ℝ => r * t) (Real.sq_sqrt hr.le)]

end Torsion.PaperExamples

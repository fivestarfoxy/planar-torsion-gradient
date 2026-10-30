module

public import Torsion.CauchyTransformExterior
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Complex.Conformal

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual Cauchy map at the compactified marked point

The coordinate is w = -1/z. The established first moment gives an actual
complex derivative at w = 0, with the normalization M/π from the paper.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The actual Cauchy map expressed in the infinity coordinate w = -1/z,
extended by its genuine zero limit at w = 0. -/
def cauchyAtInfinity (φ : ℝ → ℝ) (w : ℂ) : ℂ :=
  if w = 0 then 0 else cauchy φ (-w⁻¹)

@[simp] theorem cauchyAtInfinity_zero (φ : ℝ → ℝ) : cauchyAtInfinity φ 0 = 0 := by
  simp [cauchyAtInfinity]

theorem cauchyAtInfinity_eq {φ : ℝ → ℝ} {w : ℂ} (hw : w ≠ 0) :
    cauchyAtInfinity φ w = cauchy φ (-w⁻¹) := by
  simp [cauchyAtInfinity, hw]

/-- The conformal coordinate at the marked point has the exact derivative
M/π; this is a derivative of the concrete map, not a formal expansion. -/
theorem cauchyAtInfinity_hasDerivAt_zero {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    HasDerivAt (cauchyAtInfinity φ) ((Real.pi : ℂ)⁻¹ * (mass φ : ℂ)) 0 := by
  have hnorm : Tendsto (fun w : ℂ => ‖-w⁻¹‖) (𝓝[≠] 0) atTop := by
    simpa only [norm_neg] using (NormedField.tendsto_norm_inv_nhdsNE_zero_atTop (α := ℂ))
  have hm := (cauchy_first_moment hφ hnorm).neg
  apply hasDerivAt_iff_tendsto_slope_zero.2
  have heq : (fun w : ℂ => w⁻¹ • (cauchyAtInfinity φ (0 + w) - cauchyAtInfinity φ 0))
      =ᶠ[𝓝[≠] 0] (fun w : ℂ => -((-w⁻¹) * cauchy φ (-w⁻¹))) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : w ≠ 0 := by simpa using hw
    simp [cauchyAtInfinity_eq hw', smul_eq_mul]
  simpa only [neg_mul, neg_neg] using hm.congr' heq.symm

/-- Positive profiles give a nonzero derivative at infinity. -/
theorem cauchyAtInfinity_deriv_zero_ne {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    deriv (cauchyAtInfinity φ) 0 ≠ 0 := by
  rw [(cauchyAtInfinity_hasDerivAt_zero hφ).deriv]
  exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    (Complex.ofReal_ne_zero.mpr (mass_pos hφ hpos).ne')

/-- The infinity-coordinate extension is holomorphic on the concrete unit
ball, including its newly filled center. -/
theorem cauchyAtInfinity_differentiableOn_ball {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    DifferentiableOn ℂ (cauchyAtInfinity φ) (ball 0 1) := by
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    exact (cauchyAtInfinity_hasDerivAt_zero hφ).differentiableAt.differentiableWithinAt
  · have hnorm : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    have hz : 1 < ‖-w⁻¹‖ := by
      rw [norm_neg, norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.2 hw0)).2 hnorm
    have hd := (hasDerivAt_cauchy_exterior hφ hz).differentiableAt.comp w
      ((differentiableAt_inv hw0).neg)
    have heq : cauchyAtInfinity φ =ᶠ[𝓝 w] (fun v : ℂ => cauchy φ (-v⁻¹)) := by
      filter_upwards [eventually_ne_nhds hw0] with v hv
      exact cauchyAtInfinity_eq hv
    exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

/-- Holomorphic regularity in a neighborhood of the compactified marked
point, obtained for the actual map without any boundary regularity input. -/
theorem cauchyAtInfinity_analyticOnNhd_ball {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    AnalyticOnNhd ℂ (cauchyAtInfinity φ) (ball 0 1) :=
  (cauchyAtInfinity_differentiableOn_ball hφ).analyticOnNhd isOpen_ball

theorem cauchyAtInfinity_hasStrictDerivAt_zero {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    HasStrictDerivAt (cauchyAtInfinity φ) ((Real.pi : ℂ)⁻¹ * (mass φ : ℂ)) 0 := by
  have h := (cauchyAtInfinity_analyticOnNhd_ball hφ 0 (mem_ball_self (by norm_num : (0 : ℝ) < 1))).hasStrictFDerivAt.hasStrictDerivAt
  simpa only [fderiv_deriv, (cauchyAtInfinity_hasDerivAt_zero hφ).deriv] using h

/-- The compactified map is conformal at the marked point. -/
theorem cauchyAtInfinity_conformalAt_zero {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    ConformalAt (cauchyAtInfinity φ) 0 :=
  (cauchyAtInfinity_hasDerivAt_zero hφ).differentiableAt.conformalAt
    (cauchyAtInfinity_deriv_zero_ne hφ hpos)

end Torsion.Spectral

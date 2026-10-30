module

public import Torsion.RestrictedSpectralExteriorKernel
public import Torsion.RestrictedSpectralExteriorKernelIntegral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Genuine L¹ integrability of the actual exterior residual

The compact source formula is estimated by the ordinary endpoint quotient.
Absolute Fubini is justified by integrating the positive double-pole kernel
on the two actual exterior half-lines.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- The actual exterior residual is integrable whenever the original
source's endpoint quotient is integrable. No new residual integrability
hypothesis or formal kernel representation is introduced. -/
theorem integrable_exteriorResidualZero_of_endpoint_quotient {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f volume)
    (hq : IntegrableOn (fun s : ℝ => |f s| / (1 - |s|)) (Ioo (-1 : ℝ) 1)) :
    Integrable (exteriorResidualZero f) := by
  let μ : Measure ℝ := volume.restrict (Ioo (-1 : ℝ) 1)
  let ν : Measure ℝ := volume.restrict {y : ℝ | 1 < |y|}
  let K : ℝ × ℝ → ℝ := fun p => f p.1 / (p.2 - p.1) ^ 2
  have hfm : AEStronglyMeasurable f μ := hf.restrict
  have hKm : AEStronglyMeasurable K (μ.prod ν) := by
    dsimp only [K]
    simp only [div_eq_mul_inv]
    exact hfm.comp_fst.mul (((measurable_snd.sub measurable_fst).pow_const 2).inv.aestronglyMeasurable)
  have hKi : ∀ᵐ s : ℝ ∂μ, Integrable (fun y : ℝ => K (s, y)) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hi := integrableOn_exterior_inv_sub_sq (abs_lt.2 hs)
    simpa only [K, div_eq_mul_inv, one_div, one_mul] using hi.const_mul (f s)
  have hnorm : Integrable (fun s : ℝ => ∫ y : ℝ, ‖K (s, y)‖ ∂ν) μ := by
    apply (hq.const_mul 2).mono' hKm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hnonneg : 0 ≤ ∫ y : ℝ, ‖K (s, y)‖ ∂ν := integral_nonneg fun y => norm_nonneg _
    rw [Real.norm_of_nonneg hnonneg]
    have heq : (∫ y : ℝ, ‖K (s, y)‖ ∂ν) =
        |f s| * ∫ y : ℝ, 1 / (y - s) ^ 2 ∂ν := by
      calc
        _ = ∫ y : ℝ, |f s| * (1 / (y - s) ^ 2) ∂ν := by
          apply integral_congr_ae
          filter_upwards [] with y
          dsimp only [K]
          rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (y - s))]
          ring
        _ = _ := integral_const_mul _ _
    rw [heq]
    have hbound := integral_exterior_inv_sub_sq_le (abs_lt.2 hs)
    change |f s| * (∫ y in {y : ℝ | 1 < |y|}, 1 / (y - s) ^ 2) ≤
      2 * (|f s| / (1 - |s|))
    exact (mul_le_mul_of_nonneg_left hbound (abs_nonneg _)).trans_eq (by ring)
  have hK : Integrable K (μ.prod ν) := (integrable_prod_iff hKm).2 ⟨hKi, hnorm⟩
  have hE : MeasurableSet {y : ℝ | 1 < |y|} :=
    isOpen_lt continuous_const continuous_abs |>.measurableSet
  have hi : IntegrableOn (fun y : ℝ => (1 / Real.pi) * ∫ s in Ioo (-1 : ℝ) 1,
      f s / (y - s) ^ 2) {y : ℝ | 1 < |y|} := hK.integral_prod_right.const_mul (1 / Real.pi)
  have heq : exteriorResidualZero f = {y : ℝ | 1 < |y|}.indicator
      (fun y => (1 / Real.pi) * ∫ s in Ioo (-1 : ℝ) 1, f s / (y - s) ^ 2) := by
    funext y
    by_cases hy : 1 < |y|
    · rw [indicator_of_mem (show y ∈ {y : ℝ | 1 < |y|} from hy)]
      simp only [exteriorResidualZero, if_pos hy, exteriorResidual, integral_Icc_eq_integral_Ioo]
    · rw [indicator_of_notMem (show y ∉ {y : ℝ | 1 < |y|} from hy)]
      simp only [exteriorResidualZero, if_neg hy]
  rw [heq]
  exact (integrable_indicator_iff hE).mpr hi

end Torsion.Spectral

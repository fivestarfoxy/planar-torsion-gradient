module

public import Torsion.RestrictedSpectralSemicircle
public import Torsion.RestrictedSpectralSemicircleWeight

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Integrability of the actual endpoint quotient

The square-root barrier bounds the quotient by distance to the support
boundary by twice the already constructed integrable semicircle weight.
-/
noncomputable section
open Set Filter MeasureTheory

namespace Torsion.Spectral

/-- A genuine semicircle bound makes the endpoint quotient integrable.
The datum need only be almost everywhere strongly measurable. -/
theorem integrableOn_abs_div_one_sub_abs_of_semicircle_bound {φ : ℝ → ℝ} {C : ℝ}
    (hφ : AEStronglyMeasurable φ volume) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Ioo (-1 : ℝ) 1, |φ x| ≤ C * semicircleBarrier x) :
    IntegrableOn (fun x => |φ x| / (1 - |x|)) (Ioo (-1 : ℝ) 1) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => |φ x| / (1 - |x|)) volume := by
    simpa only [Real.norm_eq_abs, Pi.div_apply] using hφ.norm.div
      (continuous_const.sub continuous_abs).aestronglyMeasurable
  apply ((integrable_semicircleKernelWeight.const_mul (2 * C)).integrableOn).mono' hm.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hxabs : |x| < 1 := abs_lt.mpr hx
  have hd : 0 < 1 - |x| := by linarith
  have hb : 0 < semicircleBarrier x := semicircleBarrier_pos hxabs
  have hsq : semicircleBarrier x ^ 2 ≤ 2 * (1 - |x|) := by
    rw [semicircleBarrier_sq_interior hxabs]
    nlinarith [sq_nonneg (1 - |x|), sq_abs x]
  have hratio : semicircleBarrier x / (1 - |x|) ≤ 2 / semicircleBarrier x :=
    (div_le_div_iff₀ hd hb).mpr (by nlinarith [hsq])
  have hw : semicircleKernelWeight x = (semicircleBarrier x)⁻¹ := by
    unfold semicircleKernelWeight
    rw [if_pos (by linarith : |x| < 2), abs_of_pos]
    · rw [semicircleBarrier_eq_sqrt]
    · have h := (sq_lt_one_iff_abs_lt_one x).mpr hxabs
      linarith
  rw [Real.norm_of_nonneg (div_nonneg (abs_nonneg _) hd.le)]
  calc
    |φ x| / (1 - |x|) ≤ (C * semicircleBarrier x) / (1 - |x|) :=
      div_le_div_of_nonneg_right (hbound x hx) hd.le
    _ = C * (semicircleBarrier x / (1 - |x|)) := by ring
    _ ≤ C * (2 / semicircleBarrier x) := mul_le_mul_of_nonneg_left hratio hC
    _ = (2 * C) * semicircleKernelWeight x := by rw [hw]; ring

/-- The global pointwise barrier bound is a convenient sufficient input. -/
theorem integrableOn_abs_div_one_sub_abs_of_global_semicircle_bound {φ : ℝ → ℝ} {C : ℝ}
    (hφ : AEStronglyMeasurable φ volume) (hC : 0 ≤ C)
    (hbound : ∀ x : ℝ, |φ x| ≤ C * semicircleBarrier x) :
    IntegrableOn (fun x => |φ x| / (1 - |x|)) (Ioo (-1 : ℝ) 1) :=
  integrableOn_abs_div_one_sub_abs_of_semicircle_bound hφ hC (fun x _ => hbound x)

end Torsion.Spectral

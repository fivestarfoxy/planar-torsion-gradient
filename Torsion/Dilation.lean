import Torsion.Definitions
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic

/-!
# Physical dilation of planar domains

This module constructs geometric dilation and proves its area law using the
actual Lebesgue measure on the complex plane.  The operations here are not
additional hypotheses about a domain-labeling operation.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal

namespace Torsion
namespace ConvexDomain

/-- Physical dilation of a convex domain by a strictly positive real scalar. -/
def dilate (D : ConvexDomain) (s : ℝ) (hs : 0 < s) : ConvexDomain where
  carrier := s • D.carrier
  isOpen := D.isOpen.smul₀ hs.ne'
  bounded := D.bounded.smul₀ s
  convex := D.convex.smul s
  nonempty := D.nonempty.image (fun z : ℂ => s • z)

/-- The carrier is the exact complex multiplication image. -/
theorem dilate_carrier (D : ConvexDomain) (s : ℝ) (hs : 0 < s) :
    (D.dilate s hs).carrier = (fun z : ℂ => (s : ℂ) * z) '' D.carrier := by
  rfl

/-- Lebesgue area has degree two under physical planar dilation. -/
theorem dilate_area (D : ConvexDomain) (s : ℝ) (hs : 0 < s) :
    (D.dilate s hs).area = s ^ 2 * D.area := by
  change (volume (s • D.carrier)).toReal = s ^ 2 * (volume D.carrier).toReal
  rw [Measure.addHaar_smul volume, ENNReal.toReal_mul]
  change (ENNReal.ofReal |s ^ Module.finrank ℝ ℂ|).toReal * (volume D.carrier).toReal = _
  simp only [Complex.finrank_real_complex, abs_of_nonneg (sq_nonneg s),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg s)]

end ConvexDomain
/-- Exact change of variables for the inverse planar dilation. -/
theorem map_volume_inv_smul (s : ℝ) (hs : s ≠ 0) :
    Measure.map (fun z : ℂ => s⁻¹ • z) volume = ENNReal.ofReal (s ^ 2) • volume := by
  rw [Measure.map_addHaar_smul volume (inv_ne_zero hs), Complex.finrank_real_complex,
    inv_pow, inv_inv, abs_of_nonneg (sq_nonneg s)]

/-- Exact restricted change of variables; no boundary regularity is required. -/
theorem map_restrict_volume_inv_smul (s : ℝ) (hs : s ≠ 0) (D : Set ℂ) :
    Measure.map (fun z : ℂ => s⁻¹ • z) (volume.restrict (s • D)) =
      ENNReal.ofReal (s ^ 2) • volume.restrict D := by
  have he : MeasurableEmbedding (fun z : ℂ => s⁻¹ • z) :=
    (Homeomorph.smulOfNeZero s⁻¹ (inv_ne_zero hs) : ℂ ≃ₜ ℂ).toMeasurableEquiv.measurableEmbedding
  rw [← preimage_smul_inv₀ hs D, ← he.restrict_map, map_volume_inv_smul s hs,
    Measure.restrict_smul]

/-- Integral change of variables for zero-extended scalar fields. -/
theorem integral_comp_inv_smul (s : ℝ) (hs : s ≠ 0) (f : ℂ → ℝ) (D : Set ℂ) :
    (∫ z in s • D, f (s⁻¹ • z)) = s ^ 2 * ∫ x in D, f x := by
  have he : MeasurableEmbedding (fun z : ℂ => s⁻¹ • z) :=
    (Homeomorph.smulOfNeZero s⁻¹ (inv_ne_zero hs) : ℂ ≃ₜ ℂ).toMeasurableEquiv.measurableEmbedding
  rw [← he.integral_map f, map_restrict_volume_inv_smul s hs D,
    integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg s)]
  rfl

/-- Ordinary forward change of variables on the physically dilated domain. -/
theorem integral_dilate (s : ℝ) (hs : s ≠ 0) (f : ℂ → ℝ) (D : Set ℂ) :
    (∫ z in s • D, f z) = s ^ 2 * ∫ x in D, f (s • x) := by
  simpa only [smul_smul, mul_inv_cancel₀ hs, one_smul] using
    integral_comp_inv_smul s hs (fun x => f (s • x)) D

/-- Lᵖ change of variables under planar dilation, valid also for p=∞. -/
theorem eLpNorm_comp_inv_smul {E : Type*} [NormedAddCommGroup E]
    (s : ℝ) (hs : s ≠ 0) (f : ℂ → E) (p : ℝ≥0∞) (D : Set ℂ) :
    eLpNorm (fun z => f (s⁻¹ • z)) p (volume.restrict (s • D)) =
      ENNReal.ofReal (s ^ 2) ^ (1 / p).toReal * eLpNorm f p (volume.restrict D) := by
  have he : MeasurableEmbedding (fun z : ℂ => s⁻¹ • z) :=
    (Homeomorph.smulOfNeZero s⁻¹ (inv_ne_zero hs) : ℂ ≃ₜ ℂ).toMeasurableEquiv.measurableEmbedding
  change eLpNorm (f ∘ (fun z : ℂ => s⁻¹ • z)) p (volume.restrict (s • D)) = _
  rw [← he.eLpNorm_map_measure, map_restrict_volume_inv_smul s hs D,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_ne_zero hs))]
  rfl

/-- The L² dilation factor is the ordinary positive length scale. -/
theorem eLpNorm_two_comp_inv_smul {E : Type*} [NormedAddCommGroup E]
    (s : ℝ) (hs : 0 < s) (f : ℂ → E) (D : Set ℂ) :
    eLpNorm (fun z => f (s⁻¹ • z)) 2 (volume.restrict (s • D)) =
      ENNReal.ofReal s * eLpNorm f 2 (volume.restrict D) := by
  rw [eLpNorm_comp_inv_smul s hs.ne']
  congr 1
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg s) (by positivity),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq hs.le]

/-- Essential supremum is unchanged by precomposing with the inverse dilation. -/
theorem eLpNorm_top_comp_inv_smul {E : Type*} [NormedAddCommGroup E]
    (s : ℝ) (hs : s ≠ 0) (f : ℂ → E) (D : Set ℂ) :
    eLpNorm (fun z => f (s⁻¹ • z)) ∞ (volume.restrict (s • D)) =
      eLpNorm f ∞ (volume.restrict D) := by
  rw [eLpNorm_comp_inv_smul s hs]
  simp

/-- Lᵖ membership is preserved by inverse dilation. -/
theorem memLp_comp_inv_smul {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} {p : ℝ≥0∞} {D : Set ℂ}
    (hf : MemLp f p (volume.restrict D)) (s : ℝ) (hs : s ≠ 0) :
    MemLp (fun z => f (s⁻¹ • z)) p (volume.restrict (s • D)) := by
  have he : MeasurableEmbedding (fun z : ℂ => s⁻¹ • z) :=
    (Homeomorph.smulOfNeZero s⁻¹ (inv_ne_zero hs) : ℂ ≃ₜ ℂ).toMeasurableEquiv.measurableEmbedding
  apply he.memLp_map_measure_iff.mp
  rw [map_restrict_volume_inv_smul s hs D]
  exact hf.smul_measure ENNReal.ofReal_ne_top

/-- The scaled torsion candidate in the weak change-of-variables argument. -/
def scaledValue (s : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  s ^ 2 * u (s⁻¹ • z)

/-- The corresponding scaled weak-gradient candidate. -/
def scaledGradient (s : ℝ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  s • g (s⁻¹ • z)

/-- The actual essential-supremum scaling law for a scaled vector field. -/
theorem eLpNorm_top_scaledGradient (s : ℝ) (hs : 0 < s)
    (g : ℂ → ℂ) (D : Set ℂ) :
    eLpNorm (scaledGradient s g) ∞ (volume.restrict (s • D)) =
      ENNReal.ofReal s * eLpNorm g ∞ (volume.restrict D) := by
  change eLpNorm (s • (fun z : ℂ => g (s⁻¹ • z))) ∞ _ = _
  rw [eLpNorm_const_smul, eLpNorm_top_comp_inv_smul s hs.ne', Real.enorm_eq_ofReal hs.le]

/-- The ordinary chain rule for the scaled smooth approximants used in H¹₀. -/
theorem hasGradientAt_scaledValue (s : ℝ) (hs : s ≠ 0) (u : ℂ → ℝ) (z : ℂ)
    (hu : DifferentiableAt ℝ u (s⁻¹ • z)) :
    HasGradientAt (scaledValue s u) (scaledGradient s (gradient u) z) z := by
  apply hasGradientAt_iff_hasFDerivAt.2
  have hi : HasFDerivAt (fun y : ℂ => s⁻¹ • y)
      (s⁻¹ • ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).const_smul s⁻¹
  have hc := (hu.hasGradientAt.hasFDerivAt.comp z hi).const_smul (s ^ 2)
  convert hc using 1
  ext w
  simp only [scaledGradient, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    InnerProductSpace.toDual_apply, real_inner_smul_left, real_inner_smul_right,
    smul_eq_mul]
  field_simp [hs]
  ring

/-- Pointwise gradient scaling at every differentiability point. -/
theorem gradient_scaledValue (s : ℝ) (hs : s ≠ 0) (u : ℂ → ℝ) (z : ℂ)
    (hu : DifferentiableAt ℝ u (s⁻¹ • z)) :
    gradient (scaledValue s u) z = scaledGradient s (gradient u) z :=
  (hasGradientAt_scaledValue s hs u z hu).gradient

end Torsion

end

import Torsion.ShapeDeformation
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Jacobian bounds and actual L² pullback for shape changes

A positive lower bound on the actual Jacobian gives domination of the
pushforward Lebesgue measure. This proves genuine pullback membership and
norm bounds in the same concrete L² spaces used in the Sobolev graph.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Torsion.Shape

/-- A positive Jacobian lower bound controls the actual pushforward of
Lebesgue measure under an actual differentiable homeomorphism. -/
theorem map_volume_le_of_det_lower (e : Plane ≃ₜ Plane)
    {D : Plane → Plane →L[ℝ] Plane} (he : ∀ z, HasFDerivAt e (D z) z)
    {d : ℝ} (hd : 0 < d) (hdet : ∀ z, d ≤ |(D z).det|) :
    Measure.map e volume ≤ (ENNReal.ofReal d)⁻¹ • (volume : Measure Plane) := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.map_apply e.continuous.measurable hS, Measure.smul_apply]
  have hpre : MeasurableSet (e ⁻¹' S) := hS.preimage e.continuous.measurable
  have hjac := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hpre
    (fun z _ => (he z).hasFDerivWithinAt) e.injective.injOn (fun _ => (1 : ℝ≥0∞))
  rw [e.surjective.image_preimage] at hjac
  simp only [lintegral_one, mul_one, Measure.restrict_apply_univ] at hjac
  have hbound : ENNReal.ofReal d * volume (e ⁻¹' S) ≤ volume S := by
    rw [hjac]
    calc
      _ = ∫⁻ z in e ⁻¹' S, ENNReal.ofReal d ∂volume := by simp
      _ ≤ _ := lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hdet z)
  have hdiv : volume (e ⁻¹' S) ≤ volume S / ENNReal.ofReal d :=
    (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hd)) (Or.inl ENNReal.ofReal_ne_top)).mpr
    (by simpa only [mul_comm] using hbound)
  simpa only [div_eq_mul_inv, smul_eq_mul, mul_comm] using hdiv

/-- An upper bound on the forward Jacobian controls distortion of the
inverse coordinate map, without assuming a formula for its derivative. -/
theorem map_symm_volume_le_of_det_upper (e : Plane ≃ₜ Plane)
    {D : Plane → Plane →L[ℝ] Plane} (he : ∀ z, HasFDerivAt e (D z) z)
    {M : ℝ} (hdet : ∀ z, |(D z).det| ≤ M) :
    Measure.map e.symm volume ≤ ENNReal.ofReal M • (volume : Measure Plane) := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.map_apply e.symm.continuous.measurable hS, Measure.smul_apply]
  have heq : e.symm ⁻¹' S = e '' S := by
    ext z
    constructor
    · intro hz
      exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  rw [heq]
  have hjac := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun z _ => (he z).hasFDerivWithinAt) e.injective.injOn (fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_one, mul_one, Measure.restrict_apply_univ] at hjac
  rw [hjac]
  calc
    _ ≤ ∫⁻ z in S, ENNReal.ofReal M ∂volume :=
      lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hdet z)
    _ = _ := by simp

/-- Pullback preserves actual Lᵖ membership whenever the actual image measure
is bounded by a finite multiple of volume. -/
theorem memLp_pullback_of_measure_bound {E : Type*} [NormedAddCommGroup E]
    (e : Plane ≃ₜ Plane) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hmap : Measure.map e volume ≤ C • (volume : Measure Plane))
    {f : Plane → E} {p : ℝ≥0∞} (hf : MemLp f p volume) :
    MemLp (f ∘ e) p volume :=
  ((hf.smul_measure hC).mono_measure hmap).comp_of_map e.continuous.measurable.aemeasurable

/-- The corresponding exact Lᵖ bound on the concrete seminorm. -/
theorem eLpNorm_pullback_le_of_measure_bound {E : Type*} [NormedAddCommGroup E]
    (e : Plane ≃ₜ Plane) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hmap : Measure.map e volume ≤ C • (volume : Measure Plane))
    {f : Plane → E} {p : ℝ≥0∞} (hp : p ≠ ⊤) (hf : MemLp f p volume) :
    eLpNorm (f ∘ e) p volume ≤ C ^ (1 / p).toReal * eLpNorm f p volume := by
  have hm := (hf.smul_measure hC).mono_measure hmap
  rw [← eLpNorm_map_measure hm.1 e.continuous.measurable.aemeasurable]
  have hb := eLpNorm_mono_measure (p := p) f hmap
  rw [eLpNorm_smul_measure_of_ne_top hp] at hb
  exact hb

/-- Consequently every positive lower Jacobian bound gives genuine global
Lᵖ pullback, without a separate assumed composition certificate. -/
theorem memLp_pullback_of_det_lower {E : Type*} [NormedAddCommGroup E]
    (e : Plane ≃ₜ Plane) {D : Plane → Plane →L[ℝ] Plane}
    (he : ∀ z, HasFDerivAt e (D z) z)
    {d : ℝ} (hd : 0 < d) (hdet : ∀ z, d ≤ |(D z).det|)
    {f : Plane → E} {p : ℝ≥0∞} (hf : MemLp f p volume) :
    MemLp (f ∘ e) p volume :=
  memLp_pullback_of_measure_bound e
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hd))
    (map_volume_le_of_det_lower e he hd hdet) hf

end Torsion.Shape

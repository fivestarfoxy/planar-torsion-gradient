import Torsion.Dilation
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Dilation of the concrete zero-boundary Sobolev graph

The smooth test core and its simultaneous value/gradient approximations are
transported through physical dilation. No Sobolev scaling axiom is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Pointwise Topology ENNReal ContDiff

namespace Torsion

/-- The compact smooth test core is preserved by torsion scaling. -/
theorem IsTest.scaledValue {D : Set ℂ} {f : ℂ → ℝ} (hf : IsTest D f)
    (s : ℝ) (hs : s ≠ 0) : IsTest (s • D) (scaledValue s f) := by
  have hcomp : ContDiff ℝ ∞ (fun z : ℂ => f (s⁻¹ • z)) :=
    hf.1.comp (contDiff_id.const_smul s⁻¹)
  refine ⟨hcomp.const_smul (s ^ 2), ?_, ?_⟩
  · exact HasCompactSupport.mul_left (f := fun _ : ℂ => s ^ 2)
      (hf.2.1.comp_smul (inv_ne_zero hs))
  · have hsupp : tsupport (fun z : ℂ => f (s⁻¹ • z)) ⊆
        (fun z : ℂ => s⁻¹ • z) ⁻¹' tsupport f := by
      apply closure_minimal
      · intro z hz
        exact subset_tsupport f hz
      · exact (isClosed_tsupport f).preimage (continuous_id.const_smul s⁻¹)
    have hsub := tsupport_mul_subset_right (f := fun _ : ℂ => s ^ 2)
      (g := fun z : ℂ => f (s⁻¹ • z))
    change tsupport (fun z : ℂ => s ^ 2 * f (s⁻¹ • z)) ⊆ _
    refine hsub.trans (hsupp.trans ?_)
    rw [← preimage_smul_inv₀ hs D]
    exact preimage_mono hf.2.2

/-- Global L² coordinate-change formula for the zero-extended approximants. -/
theorem eLpNorm_two_comp_inv_smul_volume {E : Type*} [NormedAddCommGroup E]
    (s : ℝ) (hs : 0 < s) (f : ℂ → E) :
    eLpNorm (fun z => f (s⁻¹ • z)) 2 volume =
      ENNReal.ofReal s * eLpNorm f 2 volume := by
  simpa only [smul_set_univ₀ hs.ne', Measure.restrict_univ] using
    eLpNorm_two_comp_inv_smul s hs f Set.univ

/-- Global Lᵖ membership under inverse dilation. -/
theorem memLp_comp_inv_smul_volume {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} {p : ℝ≥0∞} (hf : MemLp f p volume)
    (s : ℝ) (hs : s ≠ 0) :
    MemLp (fun z => f (s⁻¹ • z)) p volume := by
  simpa only [smul_set_univ₀ hs, Measure.restrict_univ] using
    memLp_comp_inv_smul (hf.restrict Set.univ) s hs

/-- Dilation preserves H¹₀, with the actual scaled weak gradient. -/
theorem MemH10.dilate {D : Set ℂ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : MemH10 D u g) (s : ℝ) (hs : 0 < s) :
    MemH10 (s • D) (scaledValue s u) (scaledGradient s g) := by
  obtain ⟨hmu, hmg, f, hf, hval, hgrad⟩ := hu
  refine ⟨(memLp_comp_inv_smul_volume hmu s hs.ne').const_smul (s ^ 2),
    (memLp_comp_inv_smul_volume hmg s hs.ne').const_smul s,
    (fun n => scaledValue s (f n)), (fun n => (hf n).scaledValue s hs.ne'), ?_, ?_⟩
  · have heq (n : ℕ) :
        (fun x => scaledValue s (f n) x - scaledValue s u x) =
          (s ^ 2) • (fun x => (f n - u) (s⁻¹ • x)) := by
      funext x
      simp only [scaledValue, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    have hlim : Tendsto (fun n => (‖s ^ 2‖ₑ * ENNReal.ofReal s) *
        eLpNorm (fun x => f n x - u x) 2 volume) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul
        (a := ‖s ^ 2‖ₑ * ENNReal.ofReal s) hval
        (Or.inr (ENNReal.mul_ne_top (enorm_ne_top (x := s ^ 2)) ENNReal.ofReal_ne_top))
    convert hlim using 1
    funext n
    rw [heq n, eLpNorm_const_smul,
      eLpNorm_two_comp_inv_smul_volume s hs (f n - u)]
    exact (mul_assoc _ _ _).symm
  · have heq (n : ℕ) :
        (fun x => gradient (scaledValue s (f n)) x - scaledGradient s g x) =
          s • (fun x => (gradient (f n) - g) (s⁻¹ • x)) := by
      funext x
      rw [gradient_scaledValue s hs.ne' (f n) x
        ((hf n).1.differentiable (by simp) _)]
      simp only [scaledGradient, Pi.smul_apply, Pi.sub_apply, smul_sub]
    have hlim : Tendsto (fun n => (‖s‖ₑ * ENNReal.ofReal s) *
        eLpNorm (fun x => gradient (f n) x - g x) 2 volume) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul
        (a := ‖s‖ₑ * ENNReal.ofReal s) hgrad
        (Or.inr (ENNReal.mul_ne_top (enorm_ne_top (x := s)) ENNReal.ofReal_ne_top))
    convert hlim using 1
    funext n
    rw [heq n, eLpNorm_const_smul,
      eLpNorm_two_comp_inv_smul_volume s hs (gradient (f n) - g)]
    exact (mul_assoc _ _ _).symm

end Torsion

end

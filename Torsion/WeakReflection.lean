module

public import Torsion.WeakGradient
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Reflection of the concrete zero-boundary Sobolev graph

Complex conjugation is the reflection in the flat marked boundary.  This
module proves its measure, gradient and Sobolev transport identities directly
for the actual planar functions.  Reflection across a boundary additionally
requires a zero-trace admission argument; transport alone does not assert it.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Reflection in the real axis, acting on scalar fields. -/
def reflectedValue (u : Plane → ℝ) (z : Plane) : ℝ := u (star z)

/-- The weak gradient transformed by reflection in the real axis. -/
def reflectedGradient (g : Plane → Plane) (z : Plane) : Plane := star (g (star z))

/-- Actual planar Lebesgue measure is preserved by reflection. -/
theorem measurePreserving_conjugation :
    MeasurePreserving (star : Plane → Plane) volume volume :=
  Complex.conjLIE.measurePreserving

/-- Change of variables under planar reflection, with no integrability
assumption because the Bochner integral is total. -/
theorem integral_comp_conjugation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Plane → E) :
    (∫ z : Plane, f (star z)) = ∫ z : Plane, f z := by
  exact measurePreserving_conjugation.integral_comp'
    (f := Complex.conjCLE.toHomeomorph.toMeasurableEquiv) f

/-- Reflection preserves the exact global Lᵖ seminorm, including p = ∞. -/
theorem eLpNorm_comp_conjugation {E : Type*} [NormedAddCommGroup E]
    (f : Plane → E) (p : ℝ≥0∞) :
    eLpNorm (fun z => f (star z)) p volume = eLpNorm f p volume := by
  have he := Complex.conjCLE.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  change eLpNorm (f ∘ Complex.conjCLE.toHomeomorph.toMeasurableEquiv) p volume = _
  rw [← he.eLpNorm_map_measure]
  change eLpNorm f p (Measure.map (star : Plane → Plane) volume) = _
  rw [measurePreserving_conjugation.map_eq]

theorem memLp_reflectedValue {u : Plane → ℝ} {p : ℝ≥0∞}
    (hu : MemLp u p volume) : MemLp (reflectedValue u) p volume :=
  hu.comp_measurePreserving measurePreserving_conjugation

theorem memLp_reflectedGradient {g : Plane → Plane} {p : ℝ≥0∞}
    (hg : MemLp g p volume) : MemLp (reflectedGradient g) p volume := by
  exact Complex.conjCLE.toContinuousLinearMap.comp_memLp'
    (hg.comp_measurePreserving measurePreserving_conjugation)

theorem real_inner_conjugate_left (z w : Plane) :
    inner (𝕜 := ℝ) (star z) w = inner (𝕜 := ℝ) z (star w) := by
  simp [Complex.inner, Complex.mul_re]

/-- The classical chain rule with the actual reflected gradient. -/
theorem hasGradientAt_reflectedValue {u : Plane → ℝ} {z : Plane}
    (hu : DifferentiableAt ℝ u (star z)) :
    HasGradientAt (reflectedValue u) (reflectedGradient (gradient u) z) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := hu.hasGradientAt.hasFDerivAt.comp z Complex.conjCLE.hasFDerivAt
  convert hd using 1
  ext v
  simp only [reflectedGradient, ContinuousLinearMap.comp_apply,
    InnerProductSpace.toDual_apply, Complex.conjCLE_apply]
  exact real_inner_conjugate_left _ _

theorem gradient_reflectedValue {u : Plane → ℝ} {z : Plane}
    (hu : DifferentiableAt ℝ u (star z)) :
    gradient (reflectedValue u) z = reflectedGradient (gradient u) z :=
  (hasGradientAt_reflectedValue hu).gradient

/-- Smooth compact test functions are transported to the reflected domain. -/
theorem IsTest.reflectedValue {D : Set Plane} {f : Plane → ℝ}
    (hf : IsTest D f) : IsTest ((star : Plane → Plane) ⁻¹' D) (Torsion.reflectedValue f) := by
  refine ⟨hf.1.comp Complex.conjCLE.contDiff, ?_, ?_⟩
  · exact hf.2.1.comp_homeomorph Complex.conjCLE.toHomeomorph
  · have hsupp : tsupport (Torsion.reflectedValue f) ⊆
        (star : Plane → Plane) ⁻¹' tsupport f := by
      apply closure_minimal
      · intro z hz
        exact subset_tsupport f hz
      · exact (isClosed_tsupport f).preimage Complex.continuous_conj
    exact hsupp.trans (preimage_mono hf.2.2)

/-- Reflection transports the original H¹₀ approximation, including the
vector gradient, without any new Sobolev transformation assumption. -/
theorem MemH10.reflectedValue {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) :
    MemH10 ((star : Plane → Plane) ⁻¹' D) (Torsion.reflectedValue u) (reflectedGradient g) := by
  obtain ⟨hmu, hmg, f, hf, hv, hg⟩ := hu
  refine ⟨memLp_reflectedValue hmu, memLp_reflectedGradient hmg, fun n => Torsion.reflectedValue (f n),
    fun n => (hf n).reflectedValue, ?_, ?_⟩
  · convert hv using 1
    funext n
    exact eLpNorm_comp_conjugation (fun x => f n x - u x) 2
  · have heq (n : ℕ) :
        (fun x => gradient (Torsion.reflectedValue (f n)) x - reflectedGradient g x) =
          (fun x => star (gradient (f n) (star x) - g (star x))) := by
      funext x
      rw [gradient_reflectedValue ((hf n).1.differentiable (by simp) _)]
      simp only [reflectedGradient, star_sub]
    have hnorm (n : ℕ) :
        eLpNorm (fun x => gradient (Torsion.reflectedValue (f n)) x - reflectedGradient g x)
          2 volume = eLpNorm (fun x => gradient (f n) x - g x) 2 volume := by
      rw [heq]
      calc
        eLpNorm (fun x => star (gradient (f n) (star x) - g (star x))) 2 volume =
            eLpNorm (fun x => gradient (f n) (star x) - g (star x)) 2 volume := by
          apply eLpNorm_congr_norm_ae
          exact ae_of_all _ fun x => norm_star _
        _ = _ := eLpNorm_comp_conjugation (fun x => gradient (f n) x - g x) 2
    simpa only [hnorm] using hg

end Torsion

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Hilbert-space differentiation of Riesz data

These elementary lemmas are stated on an abstract Hilbert space so that
the material Dirichlet problem can instantiate them on its concrete
Sobolev graph without unfolding that graph during the calculus proof.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000

namespace Torsion.Shape

section Linear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Applying a fixed bounded linear map commutes with differentiation of
a real curve. This form uses only the derivative product rule. -/
theorem fixedCLM_comp_hasDerivAt (L : E →L[ℝ] F)
    {u : ℝ → E} {u' : E} {x : ℝ} (hu : HasDerivAt u u' x) :
    HasDerivAt (fun t : ℝ => L (u t)) (L u') x := by
  simpa only [ContinuousLinearMap.zero_apply, zero_add] using
    (hasDerivAt_const x L).clm_apply hu

end Linear

section Hilbert

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The real Riesz inverse as an actual bounded linear map. -/
def hilbertRieszSourceMap : NormedSpace.Dual ℝ E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Riesz identification of an actual bounded bilinear form. -/
def hilbertRieszFormMap : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ E (NormedSpace.Dual ℝ E) E)
    (hilbertRieszSourceMap E)

@[simp] theorem hilbertRieszSourceMap_apply_inner
    (f : NormedSpace.Dual ℝ E) (q : E) :
    inner (𝕜 := ℝ) (hilbertRieszSourceMap E f) q = f q :=
  InnerProductSpace.toDual_symm_apply

@[simp] theorem hilbertRieszFormMap_apply_inner
    (B : E →L[ℝ] E →L[ℝ] ℝ) (p q : E) :
    inner (𝕜 := ℝ) (hilbertRieszFormMap E B p) q = B p q :=
  InnerProductSpace.continuousLinearMapOfBilin_apply B p q

theorem hilbertRieszSourceMap_comp_hasDerivAt
    {f : ℝ → NormedSpace.Dual ℝ E} {f' : NormedSpace.Dual ℝ E} {x : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t : ℝ => hilbertRieszSourceMap E (f t))
      (hilbertRieszSourceMap E f') x :=
  fixedCLM_comp_hasDerivAt (E := NormedSpace.Dual ℝ E) (F := E)
    (hilbertRieszSourceMap E) hf

theorem hilbertRieszFormMap_comp_hasDerivAt
    {B : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {B' : E →L[ℝ] E →L[ℝ] ℝ} {x : ℝ}
    (hB : HasDerivAt B B' x) :
    HasDerivAt (fun t : ℝ => hilbertRieszFormMap E (B t))
      (hilbertRieszFormMap E B') x :=
  fixedCLM_comp_hasDerivAt (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E →L[ℝ] E)
    (hilbertRieszFormMap E) hB

end Hilbert
end Torsion.Shape

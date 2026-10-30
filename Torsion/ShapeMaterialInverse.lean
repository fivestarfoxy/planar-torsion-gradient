module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Normed.Ring.Units

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiation of an actual invertible variational operator

This elementary Banach-algebra calculation is used by the concrete shape
solution construction. The shape coefficient and forcing derivatives are
proved independently over the original H¹₀ graph before applying it.
-/

noncomputable section
open Filter
open scoped Topology

namespace Torsion.Shape

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The derivative of the genuine inverse-operator solution is the solution
of the differentiated equation, with no difference-quotient assumption. -/
theorem inverseSolution_hasDerivAt {A : ℝ → E →L[ℝ] E} {f : ℝ → E}
    {A' : E →L[ℝ] E} {f' : E}
    (hA : HasDerivAt A A' 0) (hf : HasDerivAt f f' 0) (hunit : IsUnit (A 0)) :
    HasDerivAt (fun t : ℝ => Ring.inverse (A t) (f t))
      (Ring.inverse (A 0) (f' - A' (Ring.inverse (A 0) (f 0)))) 0 := by
  obtain ⟨u, hu⟩ := hunit
  have hi : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) (↑u⁻¹) (↑u⁻¹)) (A 0) := by
    rw [← hu]
    exact hasFDerivAt_ringInverse u
  have hh := (hi.comp_hasDerivAt 0 hA).clm_apply hf
  convert hh using 1 <;> simp [← hu, Ring.inverse_unit, Function.comp_apply, ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.mul_apply,
    map_sub, sub_eq_add_neg, add_comm]

/-- Small continuous perturbations of the actual base unit remain units. -/
theorem inverseSolution_eventually_isUnit {A : ℝ → E →L[ℝ] E}
    (hA : ContinuousAt A 0) (hunit : IsUnit (A 0)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (A t) :=
  hA.tendsto.eventually (Units.isOpen.mem_nhds hunit)

/-- The inverse solutions satisfy the actual operator equation on one
parameter neighborhood, by openness of the unit group. -/
theorem inverseSolution_eventually_equation {A : ℝ → E →L[ℝ] E} {f : ℝ → E}
    (hA : ContinuousAt A 0) (hunit : IsUnit (A 0)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), A t (Ring.inverse (A t) (f t)) = f t := by
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (A t) :=
    hA.tendsto.eventually (Units.isOpen.mem_nhds hunit)
  filter_upwards [hnear] with t ht
  have h := Ring.mul_inverse_cancel (A t) ht
  exact congrArg (fun L : E →L[ℝ] E => L (f t)) h

end Torsion.Shape

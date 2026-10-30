import Torsion.SobolevAdd
import Torsion.SobolevScalar
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Smooth compact core functions and their gradients are in L²

The gradient vanishes off the topological support of its function. Consequently
its support is compact whenever the function's support is compact. Continuity
then supplies global Lᵖ membership, in particular the L² membership needed for
the Sobolev graph and its Hilbert completion.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Away from a function's topological support its gradient is zero, without
any differentiability hypothesis. -/
theorem gradient_eq_zero_of_not_mem_tsupport {f : Plane → ℝ} {x : Plane}
    (hx : x ∉ tsupport f) : gradient f x = 0 := by
  simp only [gradient, fderiv_of_not_mem_tsupport ℝ hx, map_zero]

/-- The support of a gradient is contained in the function's topological support. -/
theorem support_gradient_subset_tsupport (f : Plane → ℝ) :
    Function.support (gradient f) ⊆ tsupport f := by
  intro x hx
  by_contra h
  exact hx (gradient_eq_zero_of_not_mem_tsupport h)

/-- A compactly supported planar function has compactly supported gradient. -/
theorem hasCompactSupport_gradient {f : Plane → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (gradient f) := by
  exact hf.mono' (support_gradient_subset_tsupport f)

/-- Every smooth compact test value is globally in Lᵖ, including p = 2. -/
theorem IsTest.memLp_value {D : Set Plane} {f : Plane → ℝ} {p : ℝ≥0∞}
    (hf : IsTest D f) : MemLp f p volume :=
  hf.1.continuous.memLp_of_hasCompactSupport hf.2.1

/-- Every smooth compact test gradient is globally in Lᵖ, including p = 2. -/
theorem IsTest.memLp_gradient {D : Set Plane} {f : Plane → ℝ} {p : ℝ≥0∞}
    (hf : IsTest D f) : MemLp (gradient f) p volume :=
  hf.continuous_gradient.memLp_of_hasCompactSupport (hasCompactSupport_gradient hf.2.1)

/-- Every test function with its classical gradient is an element of the
concrete zero-boundary Sobolev graph, using the constant approximation. -/
theorem IsTest.memH10 {D : Set Plane} {f : Plane → ℝ}
    (hf : IsTest D f) : MemH10 D f (gradient f) := by
  refine ⟨hf.memLp_value, hf.memLp_gradient, (fun _ => f), (fun _ => hf), ?_, ?_⟩
  · simp
  · simp

end Torsion

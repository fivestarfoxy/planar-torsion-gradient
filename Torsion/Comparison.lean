module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Variational comparison and supermodularity

This file formalizes the algebraic part of Lemmas 3.2–3.3 and the lattice
passage used in Theorem 3.6 of `torsion-full-writeup.pdf`.

The ambient inner product is the Dirichlet energy inner product. `WeakEquation`
records the weak equation on an explicit space of admissible tests. Constructing
Sobolev positive parts, proving their admissibility, and proving their energy
identity are analytic obligations, supplied explicitly as hypotheses here.

No theorem in this file asserts existence of a weak torsion solution.
-/

namespace Torsion

/-- The truncation used for supermodularity is dominated by each original
nonnegative solution. This is the order calculation that allows the Sobolev
intersection-admissibility lemma to be applied. -/
theorem positive_defect_le_min {u₀ u₁ uU uJ : ℝ}
    (hu₀ : 0 ≤ u₀) (hu₁ : 0 ≤ u₁) (huJ : 0 ≤ uJ)
    (hU₀ : u₀ ≤ uU) (hU₁ : u₁ ≤ uU) :
    max (u₀ + u₁ - uU - uJ) 0 ≤ min u₀ u₁ := by
  apply le_min
  · exact max_le (by linarith) hu₀
  · exact max_le (by linarith) hu₁

section Variational

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A common-load weak variational equation on a specified test subspace. -/
def WeakEquation (tests : Submodule ℝ E) (load : E → ℝ) (u : E) : Prop :=
  ∀ v ∈ tests, inner (𝕜 := ℝ) u v = load v

/-- Testing with a nonnegative negative-part truncation proves that truncation
vanishes when the load is nonnegative. The signed energy identity is the
Sobolev chain-rule input. -/
theorem negative_test_eq_zero_of_weak_equation
    {tests : Submodule ℝ E} {load : E → ℝ} {u v : E}
    (hu : WeakEquation tests load u) (hv : v ∈ tests)
    (hload : 0 ≤ load v)
    (henergy : inner (𝕜 := ℝ) u v = -(‖v‖ ^ 2)) :
    v = 0 := by
  have heq := hu v hv
  have hnormle : ‖v‖ ^ 2 ≤ 0 := by linarith
  have hnorm : ‖v‖ ^ 2 = 0 := le_antisymm hnormle (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

/-- Testing the difference of two weak equations with an admissible truncation
annihilates the truncation, once its chain-rule energy identity is known. -/
theorem truncation_eq_zero_of_weak_equations
    {tests₀ tests₁ : Submodule ℝ E} {load : E → ℝ} {u₀ u₁ v : E}
    (hu₀ : WeakEquation tests₀ load u₀)
    (hu₁ : WeakEquation tests₁ load u₁)
    (hv₀ : v ∈ tests₀) (hv₁ : v ∈ tests₁)
    (henergy : inner (𝕜 := ℝ) (u₀ - u₁) v = ‖v‖ ^ 2) :
    v = 0 := by
  have hnorm : ‖v‖ ^ 2 = 0 := by
    rw [← henergy, inner_sub_left, hu₀ v hv₀, hu₁ v hv₁, sub_self]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

/-- The four weak equations used to compare the union/intersection torsion
functions force a common admissible positive-part test to vanish. -/
theorem defect_test_eq_zero_of_weak_equations
    {tests₀ tests₁ testsU testsJ : Submodule ℝ E} {load : E → ℝ}
    {u₀ u₁ uU uJ v : E}
    (hu₀ : WeakEquation tests₀ load u₀)
    (hu₁ : WeakEquation tests₁ load u₁)
    (huU : WeakEquation testsU load uU)
    (huJ : WeakEquation testsJ load uJ)
    (hv₀ : v ∈ tests₀) (hv₁ : v ∈ tests₁)
    (hvU : v ∈ testsU) (hvJ : v ∈ testsJ)
    (henergy : inner (𝕜 := ℝ) (u₀ + u₁ - uU - uJ) v = ‖v‖ ^ 2) :
    v = 0 := by
  have hnorm : ‖v‖ ^ 2 = 0 := by
    rw [← henergy, inner_sub_left, inner_sub_left, inner_add_left,
      hu₀ v hv₀, hu₁ v hv₁, huU v hvU, huJ v hvJ]
    linarith
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

variable {X : Type*}

/-- A linear realization of the energy space as real-valued representatives
turns the vanishing positive part into pointwise comparison. Applying this to
Sobolev classes requires a separate choice of representatives and the relevant
almost-everywhere or pointwise realization. -/
theorem comparison_of_admissible_positive_part
    (value : E →ₗ[ℝ] (X → ℝ))
    {tests₀ tests₁ : Submodule ℝ E} {load : E → ℝ} {u₀ u₁ v : E}
    (hu₀ : WeakEquation tests₀ load u₀)
    (hu₁ : WeakEquation tests₁ load u₁)
    (hv₀ : v ∈ tests₀) (hv₁ : v ∈ tests₁)
    (hpositive : ∀ x, value v x = max (value u₀ x - value u₁ x) 0)
    (henergy : inner (𝕜 := ℝ) (u₀ - u₁) v = ‖v‖ ^ 2) :
    ∀ x, value u₀ x ≤ value u₁ x := by
  have hv : v = 0 := truncation_eq_zero_of_weak_equations hu₀ hu₁ hv₀ hv₁ henergy
  intro x
  have hz : value v x = 0 := by simp [hv]
  have hdefect : value u₀ x - value u₁ x ≤ 0 := by
    calc
      value u₀ x - value u₁ x ≤ max (value u₀ x - value u₁ x) 0 := le_max_left _ _
      _ = value v x := (hpositive x).symm
      _ = 0 := hz
  linarith

/-- The positive part of `u₀ + u₁ - uU - uJ` gives the pointwise
supermodularity inequality after testing all four weak equations. -/
theorem supermodularity_of_admissible_positive_part
    (value : E →ₗ[ℝ] (X → ℝ))
    {tests₀ tests₁ testsU testsJ : Submodule ℝ E} {load : E → ℝ}
    {u₀ u₁ uU uJ v : E}
    (hu₀ : WeakEquation tests₀ load u₀)
    (hu₁ : WeakEquation tests₁ load u₁)
    (huU : WeakEquation testsU load uU)
    (huJ : WeakEquation testsJ load uJ)
    (hv₀ : v ∈ tests₀) (hv₁ : v ∈ tests₁)
    (hvU : v ∈ testsU) (hvJ : v ∈ testsJ)
    (hpositive : ∀ x,
      value v x = max (value u₀ x + value u₁ x - value uU x - value uJ x) 0)
    (henergy : inner (𝕜 := ℝ) (u₀ + u₁ - uU - uJ) v = ‖v‖ ^ 2) :
    ∀ x, value u₀ x + value u₁ x ≤ value uU x + value uJ x := by
  have hv : v = 0 :=
    defect_test_eq_zero_of_weak_equations hu₀ hu₁ huU huJ hv₀ hv₁ hvU hvJ henergy
  intro x
  have hz : value v x = 0 := by simp [hv]
  have hdefect : value u₀ x + value u₁ x - value uU x - value uJ x ≤ 0 := by
    calc
      value u₀ x + value u₁ x - value uU x - value uJ x ≤
          max (value u₀ x + value u₁ x - value uU x - value uJ x) 0 := le_max_left _ _
      _ = value v x := (hpositive x).symm
      _ = 0 := hz
  linarith

end Variational

section Flux

variable {X : Type*}

/-- Any monotone linear observation preserves pointwise supermodularity.
For marked flux the observation is obtained only after the required boundary
regularity and normal-derivative limit have been established. -/
theorem supermodularity_under_monotone_linear_observation
    (flux : (X → ℝ) →ₗ[ℝ] ℝ) (hflux : Monotone flux)
    {u₀ u₁ uU uJ : X → ℝ}
    (horder : ∀ x, u₀ x + u₁ x ≤ uU x + uJ x) :
    flux u₀ + flux u₁ ≤ flux uU + flux uJ := by
  have h : u₀ + u₁ ≤ uU + uJ := horder
  simpa only [map_add] using hflux h

end Flux

section RadialLattice

variable {P D : Type*} [Lattice P] [Lattice D]

/-- The step-profile convention in Theorem 3.6 preserves meets, while its join
may fill an interface slit and therefore only contains the union. Monotonicity
and domain supermodularity still imply profile supermodularity. -/
theorem supermodularity_of_lattice_comparison
    (domain : P → D) (flux : D → ℝ)
    (hmono : Monotone flux)
    (hsuper : ∀ A B, flux A + flux B ≤ flux (A ⊔ B) + flux (A ⊓ B))
    (hmeet : ∀ r s, domain (r ⊓ s) = domain r ⊓ domain s)
    (hjoin : ∀ r s, domain r ⊔ domain s ≤ domain (r ⊔ s)) :
    ∀ r s, flux (domain r) + flux (domain s) ≤
      flux (domain (r ⊔ s)) + flux (domain (r ⊓ s)) := by
  intro r s
  have hsup := hmono (hjoin r s)
  have h := hsuper (domain r) (domain s)
  rw [hmeet r s]
  linarith

end RadialLattice

end Torsion

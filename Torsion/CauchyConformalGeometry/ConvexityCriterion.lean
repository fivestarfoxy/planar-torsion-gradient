module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Convexity from supporting functionals on the actual frontier

A nonzero continuous linear functional cannot have an interior maximum on
an open set. On a bounded set in a proper normed space its maximum on the
closure is therefore attained on the frontier. This transfers supporting
inequalities from the frontier to the interior. A segment joining two
interior points cannot then leave the set through a supported frontier.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace Torsion.Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero linear functional bounded above on an open set is strictly
below that upper bound at every point of the set. -/
theorem linearFunctional_lt_on_open_of_le {D : Set E} (hD : IsOpen D)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {c : ℝ}
    (hbound : ∀ x ∈ D, ℓ x ≤ c) {x : E} (hx : x ∈ D) : ℓ x < c := by
  refine lt_of_le_of_ne (hbound x hx) ?_
  intro heq
  have hmax : IsMaxOn ℓ D x := by
    intro y hy
    exact (hbound y hy).trans_eq heq.symm
  exact hℓ ((hmax.isLocalMax (hD.mem_nhds hx)).hasFDerivAt_eq_zero ℓ.hasFDerivAt)

/-- For a nonzero continuous linear functional, an upper bound on the
frontier of an open bounded set is an upper bound on its entire closure. -/
theorem linearFunctional_le_closure_of_frontier_le [ProperSpace E]
    {D : Set E} (hD : IsOpen D) (hbounded : Bornology.IsBounded D)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {c : ℝ}
    (hbound : ∀ p ∈ frontier D, ℓ p ≤ c) {x : E} (hx : x ∈ closure D) : ℓ x ≤ c := by
  obtain ⟨p, hp, hmax⟩ := hbounded.isCompact_closure.exists_isMaxOn
    ⟨x, hx⟩ ℓ.continuous.continuousOn
  have hpnot : p ∉ D := by
    intro hpD
    have hnhds : closure D ∈ 𝓝 p := mem_of_superset (hD.mem_nhds hpD) subset_closure
    exact hℓ ((hmax.isLocalMax hnhds).hasFDerivAt_eq_zero ℓ.hasFDerivAt)
  exact (hmax hx).trans (hbound p (by rw [hD.frontier_eq]; exact ⟨hp, hpnot⟩))

/-- An open set is convex when each actual frontier point admits a strict
supporting linear functional against all interior points. Connectedness
and boundedness are unnecessary for this form of the criterion. -/
theorem convex_of_frontier_strict_support {D : Set E} (hD : IsOpen D)
    (hsupport : ∀ p ∈ frontier D, ∃ ℓ : E →L[ℝ] ℝ, ∀ x ∈ D, ℓ x < ℓ p) :
    Convex ℝ D := by
  apply convex_iff_segment_subset.2
  intro x hx y hy
  apply (convex_segment (𝕜 := ℝ) x y).isPreconnected.subset_of_closure_inter_subset hD
    ⟨x, left_mem_segment ℝ x y, hx⟩
  rintro p ⟨hpcl, hpseg⟩
  by_contra hpnot
  obtain ⟨ℓ, hℓ⟩ := hsupport p (by rw [hD.frontier_eq]; exact ⟨hpcl, hpnot⟩)
  have hhalf : Convex ℝ {z : E | ℓ z < ℓ p} :=
    (convex_Iio (ℓ p)).linear_preimage ℓ.toLinearMap
  have hp : ℓ p < ℓ p := hhalf.segment_subset (hℓ x hx) (hℓ y hy) hpseg
  exact lt_irrefl _ hp

/-- An open bounded set is convex if every frontier point has a nonzero
supporting linear functional for the actual frontier. The interior
supporting inequalities are derived, rather than added as hypotheses. -/
theorem convex_of_frontier_support [ProperSpace E] {D : Set E}
    (hD : IsOpen D) (hbounded : Bornology.IsBounded D)
    (hsupport : ∀ p ∈ frontier D, ∃ ℓ : E →L[ℝ] ℝ,
      ℓ ≠ 0 ∧ ∀ q ∈ frontier D, ℓ q ≤ ℓ p) : Convex ℝ D := by
  apply convex_of_frontier_strict_support hD
  intro p hp
  obtain ⟨ℓ, hℓ, hsupport⟩ := hsupport p hp
  refine ⟨ℓ, ?_⟩
  intro x hx
  apply linearFunctional_lt_on_open_of_le hD ℓ hℓ ?_ hx
  intro y hy
  exact linearFunctional_le_closure_of_frontier_le hD hbounded ℓ hℓ hsupport (subset_closure hy)

/-- The lower-support version, convenient for a positively oriented
boundary whose interior lies to the left of its tangent. -/
theorem convex_of_frontier_support_ge [ProperSpace E] {D : Set E}
    (hD : IsOpen D) (hbounded : Bornology.IsBounded D)
    (hsupport : ∀ p ∈ frontier D, ∃ ℓ : E →L[ℝ] ℝ,
      ℓ ≠ 0 ∧ ∀ q ∈ frontier D, ℓ p ≤ ℓ q) : Convex ℝ D := by
  apply convex_of_frontier_support hD hbounded
  intro p hp
  obtain ⟨ℓ, hℓ, hsupport⟩ := hsupport p hp
  refine ⟨-ℓ, neg_ne_zero.mpr hℓ, ?_⟩
  intro q hq
  simpa only [ContinuousLinearMap.neg_apply] using neg_le_neg (hsupport q hq)

end Torsion.Spectral

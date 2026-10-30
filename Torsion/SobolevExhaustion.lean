module

public import Torsion.SobolevGraph
public import Torsion.SobolevMonotone

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Increasing-domain density for the concrete zero-boundary Sobolev graph

This proves the density assertion used at the start of Lemma 3.7: for an
increasing sequence of open domains, the Sobolev graph of the union is exactly
the closure of the union of their Sobolev graphs. The proof uses compact support
and the defining simultaneous approximation closure, and makes no boundary
regularity assumption.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Enlarging a domain enlarges the smooth graph submodule. -/
theorem testGraphSubmodule_mono {D E : Set Plane} (hDE : D ⊆ E) :
    testGraphSubmodule D ≤ testGraphSubmodule E := by
  rintro p ⟨f, hf, hp⟩
  exact ⟨f, hf.mono hDE, hp⟩

/-- Enlarging a domain enlarges its concrete closed Sobolev graph. -/
theorem H10Graph_mono {D E : Set Plane} (hDE : D ⊆ E) : H10Graph D ≤ H10Graph E :=
  Submodule.topologicalClosure_mono (testGraphSubmodule_mono hDE)

/-- The union of the increasing-domain Sobolev spaces is dense in the Sobolev
space of their union, as asserted in Lemma 3.7 of the writeup. -/
theorem closure_iUnion_H10Graph (D : ℕ → Set Plane)
    (hD : Monotone D) (hopen : ∀ n, IsOpen (D n)) :
    closure (⋃ n, (H10Graph (D n) : Set SobolevPair)) =
      (H10Graph (⋃ n, D n) : Set SobolevPair) := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro p hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      exact H10Graph_mono (subset_iUnion D n) hn
    · exact isClosed_H10Graph _
  · change closure (testGraphSubmodule (⋃ n, D n) : Set SobolevPair) ⊆ _
    apply closure_mono
    rintro p ⟨f, hf, hp⟩
    obtain ⟨n, hn⟩ := hf.exists_mem_exhaustion hopen hD
    apply mem_iUnion.mpr
    refine ⟨n, Submodule.le_topologicalClosure _ ?_⟩
    exact ⟨f, hn, hp⟩

end Torsion

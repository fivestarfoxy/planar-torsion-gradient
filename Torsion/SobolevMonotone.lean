import Torsion.Sobolev
import Torsion.BoundedDomains
import Mathlib.Topology.Compactness.Compact

/-!
# Monotonicity and compact tests in increasing open exhaustions

The domain-monotonicity lemmas `IsTest.mono` and `MemH10.mono` are supplied by
`BoundedDomains`. Compactness of each actual test support proves that an
increasing open cover contains that test in one finite stage.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Torsion

/-- A smooth compact test in an increasing open union is supported in a single
stage of the exhaustion. -/
theorem IsTest.exists_mem_exhaustion {D : ℕ → Set Plane} {f : Plane → ℝ}
    (hf : IsTest (⋃ n, D n) f) (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D) :
    ∃ N, IsTest (D N) f := by
  obtain ⟨N, hN⟩ := hf.2.1.elim_directed_cover D hopen hf.2.2 hmono.directed_le
  exact ⟨N, hf.1, hf.2.1, hN⟩

/-- Once a compact test has entered an increasing open exhaustion it remains
admissible at every subsequent stage. -/
theorem IsTest.eventually_mem_exhaustion {D : ℕ → Set Plane} {f : Plane → ℝ}
    (hf : IsTest (⋃ n, D n) f) (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D) :
    ∀ᶠ n in atTop, IsTest (D n) f := by
  obtain ⟨N, hN⟩ := hf.exists_mem_exhaustion hopen hmono
  exact eventually_atTop.2 ⟨N, fun n hn => hN.mono (hmono hn)⟩

/-- The finite-stage form of eventual test admissibility. -/
theorem IsTest.exists_forall_ge_mem_exhaustion {D : ℕ → Set Plane} {f : Plane → ℝ}
    (hf : IsTest (⋃ n, D n) f) (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D) :
    ∃ N, ∀ n ≥ N, IsTest (D n) f := by
  obtain ⟨N, hN⟩ := hf.exists_mem_exhaustion hopen hmono
  exact ⟨N, fun n hn => hN.mono (hmono hn)⟩

end Torsion

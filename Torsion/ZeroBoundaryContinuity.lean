import Torsion.Definitions
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Continuity of a genuine zero extension from boundary limits -/

noncomputable section
open Set Filter
open scoped Topology

namespace Torsion

/-- Interior continuity and actual zero limits at the entire frontier give
global continuity of the zero extension, on any open domain. -/
theorem continuous_indicator_of_zero_boundary_tendsto
    {D : Set Plane} (hD : IsOpen D) {u : Plane → ℝ}
    (hu : ContinuousOn u D)
    (htrace : ∀ p ∈ frontier D, Tendsto u (𝓝[D] p) (𝓝 0)) :
    Continuous (D.indicator u) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p ∈ D
  · have h := (hu p hp).continuousAt (hD.mem_nhds hp)
    apply h.congr_of_eventuallyEq
    filter_upwards [hD.mem_nhds hp] with z hz
    exact indicator_of_mem hz u
  · rw [ContinuousAt, indicator_of_not_mem hp u]
    by_cases hpc : p ∈ closure D
    · have hpf : p ∈ frontier D := by
        rw [hD.frontier_eq]
        exact ⟨hpc, hp⟩
      have hi : Tendsto (D.indicator u) (𝓝[D] p) (𝓝 0) := by
        apply (htrace p hpf).congr'
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (indicator_of_mem hz u).symm
      have ho : Tendsto (D.indicator u) (𝓝[Dᶜ] p) (𝓝 0) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (indicator_of_not_mem hz u).symm
      have h := tendsto_sup.mpr ⟨hi, ho⟩
      simpa only [← nhdsWithin_union, union_compl_self, nhdsWithin_univ] using h
    · apply tendsto_const_nhds.congr'
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hpc] with z hz
      exact (indicator_of_not_mem (fun hzD => hz (subset_closure hzD)) u).symm

end Torsion

module

public import Torsion.ClassicalWeakTorsion

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Vanishing of the classical gradient on a zero level

Compact smooth localization and the proved Sobolev lattice rule give this
almost-everywhere statement on arbitrary open sets. No trace or boundary
regularity assumption is used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion

/-- The actual classical gradient of a smooth interior function is zero
almost everywhere on its zero level, even on an unbounded irregular open set. -/
theorem ContDiffOn.gradient_ae_zero_on_zero {D : Set Plane} (hD : IsOpen D)
    {u : Plane → ℝ} (hu : ContDiffOn ℝ ∞ u D) :
    ∀ᵐ x ∂volume.restrict D, u x = 0 → gradient u x = 0 := by
  classical
  have hlocal (x : D) : ∃ η : Plane → ℝ, IsTest D η ∧
      η =ᶠ[𝓝 (x : Plane)] (fun _ => 1) := by
    obtain ⟨η, hη, hone⟩ := exists_test_eq_one_near_compact hD
      (isCompact_singleton : IsCompact {(x : Plane)}) (singleton_subset_iff.mpr x.2)
    refine ⟨η, hη, ?_⟩
    simpa only [nhdsSet_singleton, Filter.EventuallyEq] using hone
  choose η hη hone using hlocal
  let W (x : D) : Set Plane := D ∩ interior {y | η x y = 1}
  have hWopen (x : D) : IsOpen (W x) := hD.inter isOpen_interior
  have hWx (x : D) : (x : Plane) ∈ W x :=
    ⟨x.2, mem_interior_iff_mem_nhds.mpr (hone x)⟩
  have hcover : (⋃ x : D, W x) = D := by
    apply Subset.antisymm
    · exact iUnion_subset (fun _ => inter_subset_left)
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hWx ⟨x, hx⟩⟩
  obtain ⟨S, hS, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWopen
  rw [← hcover, ← hSU]
  apply (ae_restrict_biUnion_iff W hS _).mpr
  intro x _hx
  have hf := (hη x).mul_contDiffOn hD hu
  have hzero := hf.memH10.gradient_ae_zero_on_zero
  apply (ae_restrict_iff' (hWopen x).measurableSet).mpr
  filter_upwards [hzero] with y hy hyW hy0
  have heq : (fun z => η x z * u z) =ᶠ[𝓝 y] u := by
    filter_upwards [isOpen_interior.mem_nhds hyW.2] with z hz
    have hz' : η x z = 1 := (interior_subset :
      interior {y : Plane | η x y = 1} ⊆ {y : Plane | η x y = 1}) hz
    simp [hz']
  have hgrad : gradient (fun z => η x z * u z) y = gradient u y := by
    unfold gradient
    rw [heq.fderiv_eq]
  rw [← hgrad]
  exact hy (by simp [hy0])

end Torsion

import Torsion.WeakTorsionInterior

/-!
# A smooth interior representative of every actual weak torsion solution

Local Weyl representatives agree on overlaps by equality of their original
almost-everywhere value classes. Gluing them preserves both the value and
the actual supplied weak gradient. The zero extension is defined here;
continuity at the boundary is a separate question.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Choosing an actual zero-extension representative preserves the original
weak torsion equation and Sobolev graph, without a boundary trace premise. -/
theorem IsWeakTorsion.of_zero_extension_representative
    {D : Set Plane} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : MeasurableSet D)
    (hrep : u =ᵐ[volume.restrict D] U) (hzero : ∀ x ∉ D, U x = 0) :
    IsWeakTorsion D U g := by
  have hi := (ae_restrict_iff' hD).mp hrep
  have ho := (ae_restrict_iff' hD.compl).mp hu.1.value_ae_zero_off
  have heq : u =ᵐ[volume] U := by
    filter_upwards [hi, ho] with x hx hox
    by_cases hxD : x ∈ D
    · exact hx hxD
    · rw [hox hxD, hzero x hxD]
      rfl
  exact ⟨hu.1.congr heq EventuallyEq.rfl, hu.2⟩

/-- The original weak torsion pair has one globally defined representative
smooth throughout its domain and zero outside it. Its classical gradient
agrees with the actual weak gradient almost everywhere in the domain. -/
theorem IsWeakTorsion.exists_smooth_representative
    {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : IsOpen D) (hb : Bornology.IsBounded D) :
    ∃ U : Plane → ℝ, ContDiffOn ℝ ∞ U D ∧
      (∀ x ∉ D, U x = 0) ∧
      (u =ᵐ[volume.restrict D] U) ∧
      (g =ᵐ[volume.restrict D] gradient U) := by
  classical
  have hlocal (x : D) := hu.exists_smooth_interior_representative hD hb x.2
  choose r v hr hv hball hvalue hgrad using hlocal
  let W (x : D) : Set Plane := Metric.ball (x : Plane) (r x)
  let U : Plane → ℝ := fun y => if hy : y ∈ D then v ⟨y, hy⟩ y else 0
  have hWopen (x : D) : IsOpen (W x) := Metric.isOpen_ball
  have hmatch (x : D) (y : Plane) (hy : y ∈ W x) : U y = v x y := by
    have hyD : y ∈ D := hball x hy
    let yD : D := ⟨y, hyD⟩
    have hyo : y ∈ W yD := Metric.mem_ball_self (hr yD)
    have hya : u =ᵐ[volume.restrict (W x ∩ W yD)] v yD :=
      ae_restrict_of_ae_restrict_of_subset
        (inter_subset_right : W x ∩ W yD ⊆ W yD) (hvalue yD)
    have hxa : u =ᵐ[volume.restrict (W x ∩ W yD)] v x :=
      ae_restrict_of_ae_restrict_of_subset
        (inter_subset_left : W x ∩ W yD ⊆ W x) (hvalue x)
    have heqAE : v yD =ᵐ[volume.restrict (W x ∩ W yD)] v x := hya.symm.trans hxa
    have heq := Measure.eqOn_open_of_ae_eq heqAE ((hWopen x).inter (hWopen yD))
      (hv yD).continuous.continuousOn (hv x).continuous.continuousOn
    have hyEq := heq (show y ∈ W x ∩ W yD from ⟨hy, hyo⟩)
    simpa only [U, dif_pos hyD] using hyEq
  have hnear (x : D) {y : Plane} (hy : y ∈ W x) : U =ᶠ[𝓝 y] v x := by
    filter_upwards [(hWopen x).mem_nhds hy] with z hz
    exact hmatch x z hz
  have hsmooth : ContDiffOn ℝ ∞ U D := by
    intro y hy
    let x : D := ⟨y, hy⟩
    exact ((hv x).contDiffAt.congr_of_eventuallyEq
      (hnear x (Metric.mem_ball_self (hr x)))).contDiffWithinAt
  have hcover : (⋃ x : D, W x) = D := by
    apply Subset.antisymm
    · exact iUnion_subset hball
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨S, hS, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWopen
  have hAE : ∀ᵐ y ∂volume.restrict D, u y = U y ∧ g y = gradient U y := by
    rw [← hcover, ← hSU]
    apply (ae_restrict_biUnion_iff W hS _).mpr
    intro x _hx
    filter_upwards [hvalue x, hgrad x, ae_restrict_mem (hWopen x).measurableSet]
      with y hy hg hyW
    refine ⟨hy.trans (hmatch x y hyW).symm, ?_⟩
    rw [(hnear x hyW).gradient_eq]
    exact hg
  refine ⟨U, hsmooth, ?_, ?_, ?_⟩
  · intro x hx
    simp only [U, dif_neg hx]
  · filter_upwards [hAE] with x hx
    exact hx.1
  · filter_upwards [hAE] with x hx
    exact hx.2

/-- A continuous representative of the actual nonnegative weak solution is
nonnegative at every interior point. -/
theorem IsWeakTorsion.nonneg_on_representative
    {D : Set Plane} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : IsOpen D) (hb : Bornology.IsBounded D)
    (hU : ContinuousOn U D) (hrep : u =ᵐ[volume.restrict D] U) :
    ∀ x ∈ D, 0 ≤ U x := by
  have hpos : ∀ᵐ x ∂volume.restrict D, 0 ≤ U x := by
    filter_upwards [ae_restrict_of_ae (hu.nonneg_ae hb), hrep] with x hx heq
    exact heq ▸ hx
  have heq : (fun x => max (0 : ℝ) (U x)) =ᵐ[volume.restrict D] U := by
    filter_upwards [hpos] with x hx
    exact max_eq_right hx
  have hpoint := Measure.eqOn_open_of_ae_eq heq hD (continuousOn_const.sup hU) hU
  intro x hx
  exact max_eq_right_iff.mp (hpoint hx)

/-- A smooth representative satisfies the genuine compact-test equation
with its classical gradient. This is an identification theorem for the
existing weak solution, not an additional PDE premise. -/
theorem IsWeakTorsion.representative_smooth_test_equation
    {D : Set Plane} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : MeasurableSet D)
    (hgrad : g =ᵐ[volume.restrict D] gradient U)
    {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    (∫ x, inner (𝕜 := ℝ) (gradient U x) (gradient ψ x)) = ∫ x, ψ x := by
  rw [← hu.global_smooth_test_equation hψ]
  apply integral_congr_ae
  have hg := (ae_restrict_iff' hD).mp hgrad
  filter_upwards [hg] with x hx
  by_cases hxD : x ∈ D
  · rw [hx hxD]
  · rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hxD (hψ.2.2 h))]
    simp

end Torsion

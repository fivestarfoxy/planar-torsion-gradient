module

public import Torsion.WeakHarmonicWeyl.Representative

@[expose] public section

/-! # An interior harmonic representative on an open set

Local Weyl representatives of the same weak function coincide on overlaps.
A countable subcover identifies their glued function with the weak value class. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion
open WeakHarmonicRegularity

/-- Every weak harmonic function in the Sobolev graph has a smooth representative
whose classical Laplacian vanishes everywhere in the open set. -/
theorem IsWeakHarmonicOn.exists_smooth_harmonic_representative
    {U E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hw : IsWeakHarmonicOn U u g) (hu : MemH10 E u g) (hU : IsOpen U) :
    ∃ H : Plane → ℝ, ContDiffOn ℝ ∞ H U ∧ (u =ᵐ[volume.restrict U] H) ∧
      ∀ z ∈ U, planarLaplacian H z = 0 := by
  classical
  have hlocal (x : U) : ∃ (r : ℝ) (v : Plane → ℝ), 0 < r ∧ ContDiff ℝ ∞ v ∧
      Metric.ball (x : Plane) r ⊆ U ∧ (u =ᵐ[volume.restrict (Metric.ball (x : Plane) r)] v) ∧
      ∀ z ∈ Metric.ball (x : Plane) r, planarLaplacian v z = 0 := by
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU x.val x.property
    have hr : 0 < δ / 4 := by positivity
    obtain ⟨v, hv, huv, _, hh⟩ := hw.exists_smooth_harmonicRepresentative_on_ball hu hr
      (by simpa only [show 4 * (δ / 4) = δ by ring] using hδU)
    exact ⟨_, v, half_pos hr, hv, (Metric.ball_subset_ball (by linarith)).trans hδU, huv, hh⟩
  choose r v hr hv hball hvalue hlap using hlocal
  let W (x : U) : Set Plane := Metric.ball (x : Plane) (r x)
  let H : Plane → ℝ := fun y => if hy : y ∈ U then v ⟨y, hy⟩ y else 0
  have hWopen (x : U) : IsOpen (W x) := Metric.isOpen_ball
  have hmatch (x : U) (y : Plane) (hy : y ∈ W x) : H y = v x y := by
    have hyU : y ∈ U := hball x hy
    let yU : U := ⟨y, hyU⟩
    have hyo : y ∈ W yU := Metric.mem_ball_self (hr yU)
    have hya : u =ᵐ[volume.restrict (W x ∩ W yU)] v yU :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hvalue yU)
    have hxa : u =ᵐ[volume.restrict (W x ∩ W yU)] v x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hvalue x)
    have heq := Measure.eqOn_open_of_ae_eq (hya.symm.trans hxa) ((hWopen x).inter (hWopen yU))
      (hv yU).continuous.continuousOn (hv x).continuous.continuousOn
    simpa only [H, dite_eq_left hyU] using heq (show y ∈ W x ∩ W yU from ⟨hy, hyo⟩)
  have hnear (x : U) {y : Plane} (hy : y ∈ W x) : H =ᶠ[𝓝 y] v x := by
    filter_upwards [(hWopen x).mem_nhds hy] with z hz
    exact hmatch x z hz
  refine ⟨H, ?_, ?_, ?_⟩
  · intro y hy
    let x : U := ⟨y, hy⟩
    exact ((hv x).contDiffAt.congr_of_eventuallyEq
      (hnear x (Metric.mem_ball_self (hr x)))).contDiffWithinAt
  · have hcover : (⋃ x : U, W x) = U :=
      Subset.antisymm (iUnion_subset hball)
        (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩)
    obtain ⟨S, hS, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWopen
    rw [← hcover, ← hSU]
    apply (ae_restrict_biUnion_iff W hS _).mpr
    intro x _
    filter_upwards [hvalue x, ae_restrict_mem (hWopen x).measurableSet] with y hy hyW
    exact hy.trans (hmatch x y hyW).symm
  · intro y hy
    let x : U := ⟨y, hy⟩
    have hyW : y ∈ W x := Metric.mem_ball_self (hr x)
    unfold planarLaplacian planarDivergence
    rw [(hnear x hyW).gradient.fderiv_eq]
    exact hlap x y hyW

end Torsion

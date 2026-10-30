import Torsion.ClassicalWeakLaplacian
import Torsion.WeakHarmonicWeyl.Classical

/-! # Genuine compact bounds from local smooth extensions -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Torsion

/-- Local bounds within a domain, at every point of a compact set, give
one actual bound on the part of that compact set lying in the domain. -/
theorem exists_bound_of_compact_local_bound {D K : Set Plane} {F : Plane → ℝ}
    (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ B : ℝ, ∀ᶠ y in 𝓝[D] x, F y ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ D, y ∈ K → F y ≤ B := by
  classical
  choose b hb using fun x : K => hlocal x x.property
  let U : ∀ x ∈ K, Set Plane := fun x hx => {y | y ∈ D → F y ≤ b ⟨x, hx⟩}
  have hU (x : Plane) (hx : x ∈ K) : U x hx ∈ 𝓝 x :=
    eventually_nhdsWithin_iff.mp (hb ⟨x, hx⟩)
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover' U hU
  let B : ℝ := ∑ x ∈ s, max (b x) 0
  refine ⟨B, Finset.sum_nonneg (fun x _ => le_max_right _ _), ?_⟩
  intro y hyD hyK
  obtain ⟨x, hx, hyU⟩ := mem_iUnion₂.mp (hs hyK)
  have hbound : F y ≤ b x := hyU hyD
  exact hbound.trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun z _ => le_max_right (b z) 0) hx))

/-- A compactly supported smooth displacement times a vector field with
actual full local smooth extensions has bounded convection and classical
gradient on the original open domain. The extension is needed only on the
compact intersection of the domain closure with the displacement support. -/
theorem exists_bound_convection_of_local_extensions {D : Set Plane}
    {V G : Plane → Plane} (hD : IsOpen D)
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hG : ∀ x ∈ closure D ∩ tsupport V, ∃ H : Plane → Plane,
      ContDiffAt ℝ ∞ H x ∧ H =ᶠ[𝓝[D] x] G) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ D,
      ‖inner (𝕜 := ℝ) (V y) (G y)‖ +
        ‖gradient (fun z => inner (𝕜 := ℝ) (V z) (G z)) y‖ ≤ B := by
  let K : Set Plane := closure D ∩ tsupport V
  let f : Plane → ℝ := fun y => inner (𝕜 := ℝ) (V y) (G y)
  have hK : IsCompact K := hVc.of_isClosed_subset
    (isClosed_closure.inter (isClosed_tsupport V)) inter_subset_right
  have hlocal (x : Plane) (hx : x ∈ K) :
      ∃ B : ℝ, ∀ᶠ y in 𝓝[D] x, ‖f y‖ + ‖gradient f y‖ ≤ B := by
    obtain ⟨H, hH, heq⟩ := hG x hx
    let p : Plane → ℝ := fun y => inner (𝕜 := ℝ) (V y) (H y)
    have hp : ContDiffAt ℝ ∞ p x := hV.contDiffAt.inner ℝ hH
    have hgp : ContinuousAt (gradient p) x :=
      (InnerProductSpace.toDual ℝ Plane).symm.continuous.continuousAt.comp
        (hp.fderiv_right (m := 0) (by simp)).continuousAt
    have hcont : ContinuousAt (fun y => ‖p y‖ + ‖gradient p y‖) x :=
      hp.continuousAt.norm.add hgp.norm
    have hb : ∀ᶠ y in 𝓝 x, ‖p y‖ + ‖gradient p y‖ <
        ‖p x‖ + ‖gradient p x‖ + 1 :=
      hcont.tendsto.eventually (gt_mem_nhds (by linarith))
    have hnear : ∀ᶠ y in 𝓝 x, H =ᶠ[𝓝[D] y] G :=
      eventually_nhds_nhdsWithin.mpr heq
    refine ⟨‖p x‖ + ‖gradient p x‖ + 1, ?_⟩
    filter_upwards [hb.filter_mono nhdsWithin_le_nhds,
      hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hnearY hyD
    have heqY : H =ᶠ[𝓝 y] G := by
      rwa [nhdsWithin_eq_nhds.mpr (hD.mem_nhds hyD)] at hnearY
    have hpEq : p =ᶠ[𝓝 y] f := by
      filter_upwards [heqY] with z hz
      simp only [p, f, hz]
    rw [← hpEq.self_of_nhds, ← hpEq.gradient_eq]
    exact hy.le
  obtain ⟨B, hB, hbound⟩ := exists_bound_of_compact_local_bound hK hlocal
  refine ⟨B, hB, ?_⟩
  intro y hyD
  by_cases hyV : y ∈ tsupport V
  · exact hbound y hyD ⟨subset_closure hyD, hyV⟩
  · have hzero : f =ᶠ[𝓝 y] 0 := by
      filter_upwards [not_mem_tsupport_iff_eventuallyEq.mp hyV] with z hz
      simp [f, hz]
    have hgrad : gradient f y = 0 := by
      rw [hzero.gradient_eq]
      simp [gradient]
    change ‖f y‖ + ‖gradient f y‖ ≤ B
    rw [hzero.self_of_nhds, hgrad]
    simpa using hB

end Torsion

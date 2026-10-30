module

public import Torsion.SobolevCutoff
public import Torsion.SobolevLattice
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Data.Complex.FiniteDimensional
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Compact-support localization inside an arbitrary open domain

A smooth cutoff equal to one near a compact set localizes the actual H¹₀
graph. This is the localization needed for the admissible tests of Lemma 3.2;
it does not mistake vanishing outside a slit domain for zero trace there.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace Torsion

/-- A genuine compact smooth cutoff equal to one in a neighborhood of K. -/
theorem exists_test_eq_one_near_compact {D K : Set Plane}
    (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ η : Plane → ℝ, IsTest D η ∧ (∀ᶠ x in 𝓝ˢ K, η x = 1) := by
  classical
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_ball_lt 0 (0 : Plane)
  let B : Set Plane := D ∩ Metric.ball 0 r
  have hB : IsOpen B := hD.inter Metric.isOpen_ball
  have hKB : K ⊆ B := subset_inter hKD hKr
  obtain ⟨η, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, Plane)) hB.isClosed_compl hK.isClosed
    (disjoint_left.mpr (fun x hx hxK => hx (hKB hxK)))
  have hs : tsupport (η : Plane → ℝ) ⊆ B := by
    intro x hx
    by_contra hnot
    have hlocal : (η : Plane → ℝ) =ᶠ[𝓝 x] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hnot)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hlocal) hx
  refine ⟨η, ⟨η.contMDiff.contDiff, ?_, hs.trans inter_subset_left⟩, hone⟩
  exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Plane) r)
    ((subset_tsupport (η : Plane → ℝ)).trans
      (hs.trans (inter_subset_right.trans Metric.ball_subset_closedBall)))

/-- If value and weak gradient are supported almost everywhere in a compact
K inside an open domain D, the actual pair belongs to H¹₀(D), regardless of
the original larger domain. -/
theorem MemH10.localize_compact_inter_of_gradient_support {D E K : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 E u g) (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0)
    (hgK : ∀ᵐ x ∂volume, x ∉ K → g x = 0) : MemH10 (E ∩ D) u g := by
  obtain ⟨η, hη, hone⟩ := exists_test_eq_one_near_compact hD hK hKD
  have hηK (x : Plane) (hx : x ∈ K) : η x = 1 ∧ gradient η x = 0 := by
    have heq : η =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) :=
      hone.filter_mono (nhds_le_nhdsSet hx)
    refine ⟨heq.self_of_nhds, ?_⟩
    unfold gradient
    rw [heq.fderiv_eq]
    simp
  apply (hu.mul_test_inter hη).congr
  · filter_upwards [huK] with x hx
    by_cases hxK : x ∈ K
    · rw [(hηK x hxK).1, one_mul]
    · simp [hx hxK]
  · filter_upwards [huK, hgK] with x hux hgx
    by_cases hxK : x ∈ K
    · simp [(hηK x hxK).1, (hηK x hxK).2]
    · simp [hux hxK, hgx hxK]

/-- Localization to D without retaining the original domain in the type. -/
theorem MemH10.localize_compact {D E K : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 E u g) (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0)
    (hgK : ∀ᵐ x ∂volume, x ∉ K → g x = 0) : MemH10 D u g :=
  (hu.localize_compact_inter_of_gradient_support hD hK hKD huK hgK).mono inter_subset_right

/-- Compact value support localizes while preserving the original domain. -/
theorem MemH10.localize_compact_inter {D E K : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 E u g) (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0) : MemH10 (E ∩ D) u g := by
  apply hu.localize_compact_inter_of_gradient_support hD hK hKD huK
  filter_upwards [huK, hu.gradient_ae_zero_on_zero] with x hx hgx
  exact fun hnot => hgx (hx hnot)

/-- The weak gradient support requirement follows from the proved zero-level
gradient rule, so a.e. compact support of the value alone suffices. -/
theorem MemH10.localize_compact_value {D E K : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 E u g) (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0) : MemH10 D u g := by
  apply hu.localize_compact hD hK hKD huK
  filter_upwards [huK, hu.gradient_ae_zero_on_zero] with x hx hgx
  exact fun hnot => hgx (hx hnot)

end Torsion
end

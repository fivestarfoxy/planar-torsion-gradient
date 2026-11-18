module

public import Torsion.NormalFrame
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Sequences
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Compactness of supporting frames at equality

A radial outer approximation can change its marked point and normal at each
step. After taking a convergent subsequence of these placements, each point
of the limiting open domain belongs to all sufficiently late outer sets.
Vanishing area excess and convexity then identify the two open domains.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Torsion.ConvexDomain

/-- A point in the first open domain outside the closure of the second
would have an entire neighborhood in their difference. Convexity then
upgrades inclusion in the closure to inclusion in the open domain. -/
theorem subset_of_volume_sdiff_eq_zero (D K : ConvexDomain)
    (h : volume (D.carrier \ K.carrier) = 0) : D.carrier ⊆ K.carrier := by
  have hcl : D.carrier ⊆ closure K.carrier := by
    intro x hx
    by_contra hx'
    have hopen : IsOpen (D.carrier ∩ (closure K.carrier)ᶜ) := D.isOpen.inter isClosed_closure.isOpen_compl
    have hpos := hopen.measure_ne_zero volume
      (show (D.carrier ∩ (closure K.carrier)ᶜ).Nonempty from ⟨x, hx, hx'⟩)
    have hsub : D.carrier ∩ (closure K.carrier)ᶜ ⊆ D.carrier \ K.carrier :=
      fun _ hy => ⟨hy.1, fun hK => hy.2 (subset_closure hK)⟩
    exact hpos (measure_mono_null hsub h)
  have hi := interior_mono hcl
  rwa [D.isOpen.interior_eq, K.convex.interior_closure_eq_interior_of_nonempty_interior
    (by simpa only [K.isOpen.interior_eq] using K.nonempty), K.isOpen.interior_eq] at hi

/-- Equal finite areas and vanishing one-sided excess identify the sets. -/
theorem carrier_eq_of_area_eq_of_volume_sdiff_eq_zero (D K : ConvexDomain)
    (ha : D.area = K.area) (h : volume (D.carrier \ K.carrier) = 0) :
    D.carrier = K.carrier := by
  have hDK := D.subset_of_volume_sdiff_eq_zero K h
  have hfin := (D.bounded.measure_lt_top (μ := (volume : Measure Plane))).ne
  have hvol : volume D.carrier = volume K.carrier :=
    (ENNReal.toReal_eq_toReal_iff' hfin (K.bounded.measure_lt_top (μ := volume)).ne).mp ha
  apply subset_antisymm hDK
  apply K.subset_of_volume_sdiff_eq_zero D
  rw [measure_sdiff hDK D.isOpen.measurableSet.nullMeasurableSet hfin, hvol, tsub_self]

private theorem null_excess_of_eventual_mem (A K : Set Plane) (E : ℕ → Set Plane)
    (hmem : ∀ x ∈ A, ∀ᶠ k in atTop, x ∈ E k)
    (hvol : Tendsto (fun k => volume (E k \ K)) atTop (𝓝 0)) :
    volume (A \ K) = 0 := by
  let tailSet (j : ℕ) : Set Plane := {x | ∀ k ≥ j, x ∈ E k \ K}
  have hzero (j : ℕ) : volume (tailSet j) = 0 := by
    apply le_antisymm _ bot_le
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hvol
    filter_upwards [eventually_ge_atTop j] with k hk
    exact measure_mono (fun x hx => hx k hk)
  apply measure_mono_null _ (measure_iUnion_null hzero)
  intro x hx
  obtain ⟨j, hj⟩ := eventually_atTop.mp (hmem x hx.1)
  exact mem_iUnion.mpr ⟨j, fun k hk => ⟨hj k hk, hx.2⟩⟩

/-- Compactness of boundary marks and unit normals gives one rigid placement
of the original domain. The only size assumption on the approximants is
vanishing excess outside a fixed domain of the original area. -/
theorem exists_inNormalFrame_eq_of_outer_limit (D K : ConvexDomain)
    (ha : D.area = K.area) (p n : ℕ → Plane) (hn : ∀ k, ‖n k‖ = 1)
    (E : ℕ → Set Plane) (hp : ∀ k, p k ∈ frontier D.carrier)
    (hsub : ∀ k, (D.inNormalFrame (p k) (n k) (hn k)).carrier ⊆ E k)
    (hvol : Tendsto (fun k => volume (E k \ K.carrier)) atTop (𝓝 0)) :
    ∃ a ∈ frontier D.carrier, ∃ v : Plane, ∃ hv : ‖v‖ = 1,
      (D.inNormalFrame a v hv).carrier = K.carrier := by
  let F := frontier D.carrier ×ˢ sphere (0 : Plane) 1
  have hcp : IsCompact F :=
    (D.bounded.isCompact_closure.of_isClosed_subset isClosed_frontier
      frontier_subset_closure).prod (isCompact_sphere _ _)
  obtain ⟨b, hb, σ, hσ, hlim⟩ := hcp.tendsto_subseq (x := fun k => (p k, n k))
    (fun k => ⟨hp k, by simpa only [mem_sphere, dist_zero_right] using hn k⟩)
  have hv : ‖b.2‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hb.2
  refine ⟨b.1, hb.1, b.2, hv, ?_⟩
  apply carrier_eq_of_area_eq_of_volume_sdiff_eq_zero
  · simpa only [inNormalFrame_area] using ha
  · apply null_excess_of_eventual_mem _ _ (E ∘ σ) _ (hvol.comp hσ.tendsto_atTop)
    intro z hz
    have hzD := (D.mem_inNormalFrame _ _ _ hv).mp hz
    have hp' : Tendsto (fun k => p (σ k)) atTop (𝓝 b.1) := hlim.fst_nhds
    have hn' : Tendsto (fun k => n (σ k)) atTop (𝓝 b.2) := hlim.snd_nhds
    have hzlim : Tendsto (fun k => (-Complex.I * n (σ k)) * z + p (σ k))
        atTop (𝓝 ((-Complex.I * b.2) * z + b.1)) :=
      ((hn'.const_mul _).mul_const _).add hp'
    filter_upwards [hzlim.eventually_mem (D.isOpen.mem_nhds hzD)] with k hk
    exact hsub (σ k) ((D.mem_inNormalFrame _ _ _ _).mpr hk)

end Torsion.ConvexDomain

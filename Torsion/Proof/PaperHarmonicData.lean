module

public import Torsion.Proof.PaperHarmonicLift
public import Torsion.Proof.PaperBoundaryComparison
public import Torsion.ZeroBoundaryContinuity
public import Torsion.Proof.PaperHarmonicRepresentative

@[expose] public section

/-! # Continuous harmonic extensions of actual smooth boundary data -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion
open WeakHarmonicRegularity

private theorem continuous_harmonic_extension_of_rep (D : ConvexDomain) {b H h B : Plane → ℝ}
    (hb : IsTest univ b) (hs : ContDiffOn ℝ ∞ h D.carrier) (hH : H =ᵐ[volume.restrict D.carrier] h)
    (hl : ∀ z ∈ D.carrier, planarLaplacian h z = 0)
    (hBc : Continuous B) (hB0 : ∀ z ∉ D.carrier, B z = 0)
    (hbound : ∀ᵐ z ∂volume.restrict D.carrier, |H z - b z| ≤ B z) :
    ∃ U : Plane → ℝ, Continuous U ∧ ContDiffOn ℝ ∞ U D.carrier ∧
      (∀ z ∈ D.carrier, planarLaplacian U z = 0) ∧ (∀ z ∉ D.carrier, U z = b z) ∧
      H =ᵐ[volume.restrict D.carrier] U := by
  let w (z : Plane) := h z - b z
  have hw : ContinuousOn w D.carrier := hs.continuousOn.sub hb.1.continuous.continuousOn
  have hae : (fun z => max |w z| (B z)) =ᵐ[volume.restrict D.carrier] B := by
    filter_upwards [hbound, hH] with z h1 h2
    apply max_eq_right
    simpa only [w, ← h2] using h1
  have hpt := Measure.eqOn_open_of_ae_eq hae D.isOpen (hw.abs.sup hBc.continuousOn) hBc.continuousOn
  have htr (p) (hp : p ∈ frontier D.carrier) : Tendsto w (𝓝[D.carrier] p) (𝓝 0) := by
    apply squeeze_zero_norm' _
      (show Tendsto B (𝓝[D.carrier] p) (𝓝 0) by
        rw [← hB0 p (D.isOpen.frontier_eq ▸ hp).2]
        exact (hBc.tendsto p).mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact max_eq_right_iff.mp (hpt hz)
  let U (z : Plane) := D.carrier.indicator w z + b z
  have heq (z) (hz : z ∈ D.carrier) : U z = h z := by simp [U, hz, w]
  have hnear (z) (hz : z ∈ D.carrier) : U =ᶠ[𝓝 z] h := by
    filter_upwards [D.isOpen.mem_nhds hz] with y hy
    exact heq y hy
  refine ⟨U, (continuous_indicator_of_zero_boundary_tendsto D.isOpen hw htr).add hb.1.continuous, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (((hs z hz).contDiffAt (D.isOpen.mem_nhds hz)).congr_of_eventuallyEq (hnear z hz)).contDiffWithinAt
  · intro z hz
    have hg : gradient U =ᶠ[𝓝 z] gradient h := by
      filter_upwards [D.isOpen.mem_nhds hz] with y hy
      exact (hnear y hy).gradient_eq
    unfold planarLaplacian planarDivergence
    rw [hg.fderiv_eq]
    exact hl z hz
  · intro z hz
    simp [U, hz]
  · filter_upwards [hH, ae_restrict_mem D.isOpen.measurableSet] with z hz hD
    exact hz.trans (heq z hD).symm

/-- A continuous classical harmonic extension agrees everywhere off the open domain
with the supplied smooth data. Its integral is exactly the weak torsion flux. -/
theorem exists_continuous_harmonic_extension_with_integral (D : ConvexDomain)
    {b : Plane → ℝ} (hb : IsTest univ b) :
    ∃ H : Plane → ℝ, Continuous H ∧ ContDiffOn ℝ ∞ H D.carrier ∧
      (∀ z ∈ D.carrier, planarLaplacian H z = 0) ∧ (∀ z ∉ D.carrier, H z = b z) ∧
      ∀ {u : Plane → ℝ} {g : Plane → Plane}, IsWeakTorsion D.carrier u g →
        (∫ z in D.carrier, H z) = (∫ z in D.carrier, b z) -
          ∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (gradient b z) := by
  obtain ⟨v, G, B, hm, hh, ht, hc, hz, hB⟩ := exists_weak_harmonic_extension D hb
  obtain ⟨h, hs, ha, hl⟩ := hh.exists_smooth_harmonic_representative hm D.isOpen
  obtain ⟨H, hHc, hHs, hHl, hHz, hHa⟩ := continuous_harmonic_extension_of_rep D hb hs ha hl hc hz hB
  refine ⟨H, hHc, hHs, hHl, hHz, ?_⟩
  intro u g hu
  rw [← integral_congr_ae hHa]
  exact weak_harmonic_integral_eq_torsion_flux D hu hb hm hh ht

/-- Every smooth compactly supported boundary datum has a harmonic representative
continuous through the frontier on every bounded open convex domain. -/
theorem exists_continuous_harmonic_extension (D : ConvexDomain) {b : Plane → ℝ} (hb : IsTest univ b) :
    ∃ H : Plane → ℝ, Continuous H ∧ ContDiffOn ℝ ∞ H D.carrier ∧
      (∀ z ∈ D.carrier, planarLaplacian H z = 0) ∧ ∀ z ∉ D.carrier, H z = b z := by
  obtain ⟨H, hc, hs, hl, hz, _⟩ := exists_continuous_harmonic_extension_with_integral D hb
  exact ⟨H, hc, hs, hl, hz⟩

/-- Nonnegative boundary values give a nonnegative classical harmonic extension
throughout a bounded open domain. -/
theorem nonneg_on_of_harmonic_frontier {D : Set Plane} {H : Plane → ℝ}
    (ho : IsOpen D) (hb : Bornology.IsBounded D) (hc : Continuous H)
    (hs : ContDiffOn ℝ ∞ H D) (hl : ∀ z ∈ D, planarLaplacian H z = 0)
    (hzero : ∀ z ∈ frontier D, 0 ≤ H z) : ∀ z ∈ D, 0 ≤ H z := by
  have hmax := nonpos_on_of_compact_test_harmonic_frontier ho hb hc.neg hs.neg
    (fun z hz => neg_nonpos.mpr (hzero z hz))
  have hgrad (z : Plane) : gradient (fun y => -H y) z = -gradient H z := by
    simp [gradient, fderiv_fun_neg]
  apply fun z hz => neg_nonpos.mp (hmax ?_ z hz)
  intro ψ hψ
  change (∫ z, inner (𝕜 := ℝ) (gradient (fun y => -H y) z) (gradient ψ z)) = 0
  simp only [hgrad, inner_neg_left, integral_neg, classical_harmonic_smooth_test_equation ho hs hl hψ, neg_zero]

/-- Positive test data are realized by nonnegative harmonic functions on the
physical domain, with their exact mass given by the torsion flux. -/
theorem exists_nonneg_harmonic_extension_with_integral (D : ConvexDomain)
    {b : Plane → ℝ} (hb : IsTest univ b) (hpos : ∀ z, 0 ≤ b z) :
    ∃ H : Plane → ℝ, Continuous H ∧ ContDiffOn ℝ ∞ H D.carrier ∧
      (∀ z ∈ D.carrier, planarLaplacian H z = 0) ∧ (∀ z ∉ D.carrier, H z = b z) ∧
      (∀ z, 0 ≤ H z) ∧ ∀ {u : Plane → ℝ} {g : Plane → Plane}, IsWeakTorsion D.carrier u g →
        (∫ z in D.carrier, H z) = (∫ z in D.carrier, b z) -
          ∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (gradient b z) := by
  obtain ⟨H, hc, hs, hl, hz, he⟩ := exists_continuous_harmonic_extension_with_integral D hb
  have hf (z) (h : z ∈ frontier D.carrier) : 0 ≤ H z := by
    rw [hz _ (D.isOpen.frontier_eq ▸ h).2]
    exact hpos z
  refine ⟨H, hc, hs, hl, hz, ?_, he⟩
  intro z
  by_cases h : z ∈ D.carrier
  · exact nonneg_on_of_harmonic_frontier D.isOpen D.bounded hc hs hl hf z h
  · rw [hz _ h]
    exact hpos z

end Torsion

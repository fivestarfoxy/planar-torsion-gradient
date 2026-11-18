module

public import Torsion.ClassicalWeakTorsion
public import Torsion.Proof.PaperHarmonicRescaling
public import Torsion.Proof.PaperHarmonicRepresentative

@[expose] public section

/-! # Compact smooth harmonic approximants on a convex closure

Cut off a neighborhood solution outside a smaller neighborhood of the compact
body. Its derivatives and its classical harmonic equation are preserved there. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion.HermiteHadamard
open WeakHarmonicRegularity

/-- A function smooth on an open set has a compact smooth extension of its
restriction to a neighborhood of any compact subset. -/
theorem exists_test_agree_near_compact {K U : Set Plane} {H : Plane → ℝ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hH : ContDiffOn ℝ ∞ H U) :
    ∃ (f : Plane → ℝ) (W : Set Plane), IsTest U f ∧ IsOpen W ∧
      K ⊆ W ∧ W ⊆ U ∧ EqOn f H W := by
  obtain ⟨η, hη, hone⟩ := exists_test_eq_one_near_compact hU hK hKU
  obtain ⟨V, hV, hKV, hVone⟩ := mem_nhdsSet_iff_exists.mp hone
  exact ⟨fun x => η x * H x, V ∩ U, hη.mul_contDiffOn hU hH, hV.inter hU,
    subset_inter hKV hKU, inter_subset_right, fun x hx => by
      change η x * H x = H x
      rw [show η x = 1 from hVone hx.1, one_mul]⟩

/-- Continuous functions harmonic and smooth in a bounded convex domain
have globally smooth compactly supported approximants which are harmonic
on a neighborhood of the entire closure. -/
theorem exists_compact_harmonic_approximation (D : ConvexDomain) {H : Plane → ℝ}
    (hc : Continuous H) (hs : ContDiffOn ℝ ∞ H D.carrier)
    (hh : ∀ x ∈ D.carrier, planarLaplacian H x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : Plane → ℝ) (W : Set Plane), IsTest univ f ∧ IsOpen W ∧
      closure D.carrier ⊆ W ∧ (∀ x ∈ W, planarLaplacian f x = 0) ∧
      ∀ x ∈ closure D.carrier, |f x - H x| < ε := by
  obtain ⟨v, U, hU, hDU, _, hv, hharm, happrox⟩ :=
    exists_neighborhood_harmonic_approximation D hc hs hh hε
  obtain ⟨f, W, hf, hW, hDW, hWU, heq⟩ :=
    exists_test_agree_near_compact D.bounded.isCompact_closure hU hDU hv
  refine ⟨f, W, ⟨hf.1, hf.2.1, subset_univ _⟩, hW, hDW, ?_, ?_⟩
  · intro x hx
    have hnear : f =ᶠ[𝓝 x] v := by
      filter_upwards [hW.mem_nhds hx] with y hy
      exact heq hy
    unfold planarLaplacian planarDivergence
    rw [hnear.gradient.fderiv_eq]
    exact hharm x (hWU hx)
  · intro x hx
    rw [heq (hDW hx)]
    exact happrox x hx

/-- One-sided approximation on the closure. In particular, each approximant
is positive at every boundary point where the original datum is nonnegative. -/
theorem exists_compact_harmonic_upper_approximation (D : ConvexDomain) {H : Plane → ℝ}
    (hc : Continuous H) (hs : ContDiffOn ℝ ∞ H D.carrier)
    (hh : ∀ x ∈ D.carrier, planarLaplacian H x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : Plane → ℝ) (W : Set Plane), IsTest univ f ∧ IsOpen W ∧
      closure D.carrier ⊆ W ∧ (∀ x ∈ W, planarLaplacian f x = 0) ∧
      ∀ x ∈ closure D.carrier, H x < f x ∧ f x < H x + ε := by
  let G : Plane → ℝ := fun x => H x + ε / 2
  have hG : gradient G = gradient H := by
    funext x
    simp only [G, gradient, fderiv_add_const]
  have hGharm (x : Plane) (hx : x ∈ D.carrier) : planarLaplacian G x = 0 := by
    simpa only [planarLaplacian, hG] using hh x hx
  obtain ⟨f, W, hf, hW, hDW, hlap, hclose⟩ := exists_compact_harmonic_approximation D
    (H := G) (hc.add continuous_const) (hs.add contDiffOn_const) hGharm (half_pos hε)
  refine ⟨f, W, hf, hW, hDW, hlap, fun x hx => ?_⟩
  obtain ⟨hl, hr⟩ := abs_lt.mp (hclose x hx)
  dsimp only [G] at hl hr
  constructor <;> linarith

/-- A continuous representative of the actual weak harmonic Sobolev pair can
itself be approximated from above, uniformly on the whole closed body. -/
theorem exists_compact_upper_approximation_of_weak_harmonic (D : ConvexDomain)
    {E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} (hc : Continuous u)
    (hw : IsWeakHarmonicOn D.carrier u g) (hu : MemH10 E u g) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : Plane → ℝ) (W : Set Plane), IsTest univ f ∧ IsOpen W ∧
      closure D.carrier ⊆ W ∧ (∀ x ∈ W, planarLaplacian f x = 0) ∧
      ∀ x ∈ closure D.carrier, u x < f x ∧ f x < u x + ε := by
  obtain ⟨H, hs, hae, hh⟩ := hw.exists_smooth_harmonic_representative hu D.isOpen
  have heq : EqOn u H D.carrier :=
    Measure.eqOn_open_of_ae_eq hae D.isOpen hc.continuousOn hs.continuousOn
  refine exists_compact_harmonic_upper_approximation D hc (hs.congr heq) ?_ hε
  intro x hx
  have hnear : u =ᶠ[𝓝 x] H := by
    filter_upwards [D.isOpen.mem_nhds hx] with y hy
    exact heq hy
  unfold planarLaplacian planarDivergence
  rw [hnear.gradient.fderiv_eq]
  exact hh x hx

end Torsion.HermiteHadamard

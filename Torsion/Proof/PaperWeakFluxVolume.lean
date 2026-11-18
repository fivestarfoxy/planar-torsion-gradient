module

public import Torsion.Proof.PaperHarmonicLift
public import Torsion.DomainComparison

@[expose] public section

/-! # Moving a compact boundary test's Laplacian onto a zero-extended Sobolev value -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion.HermiteHadamard
open WeakHarmonicRegularity

theorem compactSupport_planarLaplacian {b : Plane → ℝ} (hb : HasCompactSupport b) :
    HasCompactSupport (planarLaplacian b) := by
  apply (hasCompactSupport_gradient hb).mono'
  intro x hx
  by_contra hn
  have hz := fderiv_of_notMem_tsupport ℝ hn
  exact hx (by simp [planarLaplacian, planarDivergence, hz])

private theorem real_inner_toLp_eq_integral_mul {f g : Plane → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  simp [h1, h2, mul_comm]

/-- Weak integration by parts on the full plane, valid for the actual
zero extension even when the original boundary is nonsmooth. -/
theorem integral_inner_gradient_eq_neg_laplacian {D : Set Plane} {u b : Plane → ℝ}
    {g : Plane → Plane} (hu : MemH10 D u g) (hb : IsTest univ b) :
    (∫ x, inner (𝕜 := ℝ) (gradient b x) (g x)) = -(∫ x, planarLaplacian b x * u x) := by
  have hL : MemLp (planarLaplacian b) 2 volume :=
    (continuous_planarLaplacian_of_contDiff hb.1).memLp_of_hasCompactSupport
      (compactSupport_planarLaplacian hb.2.1)
  let L : SobolevPair →L[ℝ] ℝ :=
    (innerSL ℝ (hb.memLp_gradient.toLp (gradient b))).comp (ContinuousLinearMap.snd ℝ _ _) +
    (innerSL ℝ (hL.toLp (planarLaplacian b))).comp (ContinuousLinearMap.fst ℝ _ _)
  have hker : H10Graph D ≤ LinearMap.ker L.toLinearMap := by
    apply (testGraphSubmodule D).topologicalClosure_minimal
    · rintro p ⟨v, hv, rfl⟩
      change inner (𝕜 := ℝ) ((hb.memLp_gradient (p := 2)).toLp (gradient b))
        ((hv.memLp_gradient (p := 2)).toLp (gradient v)) +
        inner (𝕜 := ℝ) (hL.toLp (planarLaplacian b)) ((hv.memLp_value (p := 2)).toLp v) = 0
      rw [inner_toLp_eq_integral_real_inner, real_inner_toLp_eq_integral_mul,
        classical_laplacian_smooth_test_equation isOpen_univ hb.1.contDiffOn (hv.mono (subset_univ _)), neg_add_cancel]
    · exact ContinuousLinearMap.isClosed_ker L
  have h := hker ((memH10_iff_mem_H10Graph hu.1 hu.2.1).mp hu)
  change inner (𝕜 := ℝ) ((hb.memLp_gradient (p := 2)).toLp (gradient b)) (hu.2.1.toLp g) +
    inner (𝕜 := ℝ) (hL.toLp (planarLaplacian b)) (hu.1.toLp u) = 0 at h
  rw [inner_toLp_eq_integral_real_inner, real_inner_toLp_eq_integral_mul] at h
  linarith

/-- Weak torsion flux tested against the global boundary datum `b`. -/
def weakBoundaryFlux (D : ConvexDomain) (g : Plane → Plane) (b : Plane → ℝ) : ℝ :=
  (∫ z in D.carrier, b z) - ∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (gradient b z)

theorem weakBoundaryFlux_eq_volume (D : ConvexDomain) {u b : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D.carrier u g) (hb : IsTest univ b) :
    weakBoundaryFlux D g b = (∫ z in D.carrier, b z) + ∫ z, u z * planarLaplacian b z := by
  have hglobal : (∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (gradient b z)) =
      ∫ z, inner (𝕜 := ℝ) (gradient b z) (g z) := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
    · exact integral_congr_ae (Eventually.of_forall fun z => real_inner_comm _ _)
    · filter_upwards [(ae_restrict_iff' D.isOpen.measurableSet.compl).mp hu.gradient_ae_zero_off] with z hz hc
      simp [show g z = 0 from hz hc]
  unfold weakBoundaryFlux
  rw [hglobal, integral_inner_gradient_eq_neg_laplacian hu hb, sub_neg_eq_add]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)

end Torsion.HermiteHadamard

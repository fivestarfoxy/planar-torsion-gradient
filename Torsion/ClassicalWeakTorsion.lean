module

public import Torsion.WeakHarmonicWeyl
public import Torsion.HilbertDirichlet

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual classical Poisson data identify weak H¹₀ torsion

A compact cutoff localizes the classical gradient near each smooth test.
Coordinatewise integration by parts gives the genuine smooth-test equation.
The proved closed Sobolev graph then extends it to every H¹₀ test, using the
already constructed bounded-domain Dirichlet solution as a reference.
No weak-test equation is assumed in the final theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Multiplication by a compact smooth cutoff supported in an open region
turns locally smooth data into an actual global compact test function. -/
theorem IsTest.mul_contDiffOn {D : Set Plane} {η f : Plane → ℝ}
    (hη : IsTest D η) (hD : IsOpen D) (hf : ContDiffOn ℝ ∞ f D) :
    IsTest D (fun x => η x * f x) := by
  refine ⟨?_, hη.2.1.mul_right, tsupport_mul_subset_left.trans hη.2.2⟩
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ D
  · exact hη.1.contDiffAt.mul ((hf x hx).contDiffAt (hD.mem_nhds hx))
  · have hnot : x ∉ tsupport η := fun h => hx (hη.2.2 h)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have heq : η =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
    filter_upwards [heq] with y hy
    simp [hy]

/-- Smoothness of the actual gradient on an arbitrary open region. -/
theorem contDiffOn_gradient_of_isOpen {D : Set Plane} {u : Plane → ℝ}
    (hu : ContDiffOn ℝ ∞ u D) (hD : IsOpen D) : ContDiffOn ℝ ∞ (gradient u) D :=
  (InnerProductSpace.toDual ℝ Plane).symm.contDiff.comp_contDiffOn
    (hu.fderiv_of_isOpen hD (by simp))

private theorem continuous_directional {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : Plane) : Continuous (fun x => fderiv ℝ f x v) :=
  (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp (hf.continuous_fderiv (by simp))

/-- Classical planar Poisson data give the actual full-plane smooth-test
equation.  Both integrations by parts use genuine global compact tests,
obtained by localizing the classical gradient near the test support. -/
theorem classical_poisson_smooth_test_equation {D : Set Plane} {u ψ : Plane → ℝ}
    (hD : IsOpen D) (hu : ContDiffOn ℝ ∞ u D)
    (hlap : ∀ x ∈ D, WeakHarmonicRegularity.planarLaplacian u x = -1)
    (hψ : IsTest D ψ) :
    (∫ x, inner (𝕜 := ℝ) (gradient u x) (gradient ψ x)) = ∫ x, ψ x := by
  obtain ⟨η, hη, hone⟩ := exists_test_eq_one_near_compact hD hψ.2.1 hψ.2.2
  let G : Plane → Plane := gradient u
  have hG : ContDiffOn ℝ ∞ G D := contDiffOn_gradient_of_isOpen hu hD
  let f₁ : Plane → ℝ := fun x => η x * (G x).re
  let f₂ : Plane → ℝ := fun x => η x * (G x).im
  have hf₁ : IsTest D f₁ := hη.mul_contDiffOn hD (Complex.reCLM.contDiff.comp_contDiffOn hG)
  have hf₂ : IsTest D f₂ := hη.mul_contDiffOn hD (Complex.imCLM.contDiff.comp_contDiffOn hG)
  have hηone {x : Plane} (hx : x ∈ tsupport ψ) : η =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) :=
    hone.filter_mono (nhds_le_nhdsSet hx)
  have hlocal₁ {x : Plane} (hx : x ∈ tsupport ψ) :
      fderiv ℝ f₁ x (1 : Plane) = (fderiv ℝ G x (1 : Plane)).re := by
    have heq : f₁ =ᶠ[𝓝 x] fun y => (G y).re := by
      filter_upwards [hηone hx] with y hy
      simp [f₁, hy]
    have hdiff : DifferentiableAt ℝ G x :=
      ((hG x (hψ.2.2 hx)).contDiffAt (hD.mem_nhds (hψ.2.2 hx))).differentiableAt (by simp)
    rw [heq.fderiv_eq]
    change fderiv ℝ ((Complex.reCLM : Plane →L[ℝ] ℝ) ∘ G) x (1 : Plane) = _
    rw [(Complex.reCLM.hasFDerivAt.comp x hdiff.hasFDerivAt).fderiv]
    rfl
  have hlocal₂ {x : Plane} (hx : x ∈ tsupport ψ) :
      fderiv ℝ f₂ x Complex.I = (fderiv ℝ G x Complex.I).im := by
    have heq : f₂ =ᶠ[𝓝 x] fun y => (G y).im := by
      filter_upwards [hηone hx] with y hy
      simp [f₂, hy]
    have hdiff : DifferentiableAt ℝ G x :=
      ((hG x (hψ.2.2 hx)).contDiffAt (hD.mem_nhds (hψ.2.2 hx))).differentiableAt (by simp)
    rw [heq.fderiv_eq]
    change fderiv ℝ ((Complex.imCLM : Plane →L[ℝ] ℝ) ∘ G) x Complex.I = _
    rw [(Complex.imCLM.hasFDerivAt.comp x hdiff.hasFDerivAt).fderiv]
    rfl
  have hleftPoint (x : Plane) : inner (𝕜 := ℝ) (gradient u x) (gradient ψ x) =
      f₁ x * fderiv ℝ ψ x (1 : Plane) + f₂ x * fderiv ℝ ψ x Complex.I := by
    by_cases hx : x ∈ tsupport ψ
    · have hy := (hηone hx).self_of_nhds
      simp only [f₁, f₂, G, hy, one_mul, fderiv_apply_eq_inner_gradient, Complex.inner,
        Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, zero_sub, neg_neg]
      ring
    · simp [fderiv_apply_eq_inner_gradient, gradient_eq_zero_of_not_mem_tsupport hx]
  have hrightPoint (x : Plane) :
      fderiv ℝ f₁ x (1 : Plane) * ψ x + fderiv ℝ f₂ x Complex.I * ψ x = -ψ x := by
    by_cases hx : x ∈ tsupport ψ
    · have hh : fderiv ℝ f₁ x (1 : Plane) + fderiv ℝ f₂ x Complex.I = -1 := by
        rw [hlocal₁ hx, hlocal₂ hx]
        exact hlap x (hψ.2.2 hx)
      calc
        _ = (fderiv ℝ f₁ x (1 : Plane) + fderiv ℝ f₂ x Complex.I) * ψ x := by ring
        _ = -ψ x := by rw [hh]; ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hL₁ : Integrable (fun x => f₁ x * fderiv ℝ ψ x (1 : Plane)) :=
    (hf₁.1.continuous.mul (continuous_directional hψ.1 1)).integrable_of_hasCompactSupport
      hf₁.2.1.mul_right
  have hL₂ : Integrable (fun x => f₂ x * fderiv ℝ ψ x Complex.I) :=
    (hf₂.1.continuous.mul (continuous_directional hψ.1 Complex.I)).integrable_of_hasCompactSupport
      hf₂.2.1.mul_right
  have hR₁ : Integrable (fun x => fderiv ℝ f₁ x (1 : Plane) * ψ x) :=
    ((continuous_directional hf₁.1 1).mul hψ.1.continuous).integrable_of_hasCompactSupport
      hψ.2.1.mul_left
  have hR₂ : Integrable (fun x => fderiv ℝ f₂ x Complex.I * ψ x) :=
    ((continuous_directional hf₂.1 Complex.I).mul hψ.1.continuous).integrable_of_hasCompactSupport
      hψ.2.1.mul_left
  have hi₁ := hf₁.memH10.distributionalGradient ψ hψ.1 hψ.2.1 (1 : Plane)
  have hi₂ := hf₂.memH10.distributionalGradient ψ hψ.1 hψ.2.1 Complex.I
  simp only [← fderiv_apply_eq_inner_gradient] at hi₁ hi₂
  have hRsum : (∫ x, fderiv ℝ f₁ x (1 : Plane) * ψ x) +
      (∫ x, fderiv ℝ f₂ x Complex.I * ψ x) = -(∫ x, ψ x) := by
    rw [← integral_add hR₁ hR₂]
    simp_rw [hrightPoint]
    exact integral_neg ψ
  calc
    _ = ∫ x, f₁ x * fderiv ℝ ψ x (1 : Plane) + f₂ x * fderiv ℝ ψ x Complex.I :=
      integral_congr_ae (ae_of_all _ hleftPoint)
    _ = (∫ x, f₁ x * fderiv ℝ ψ x (1 : Plane)) +
        (∫ x, f₂ x * fderiv ℝ ψ x Complex.I) := integral_add hL₁ hL₂
    _ = ∫ x, ψ x := by linarith

/-- Smooth-test equations determine the genuine weak equation on the
entire concrete Sobolev graph.  The reference weak solution is constructed
by the proved Lax--Milgram development; its difference is tested using the
proved closed-graph density theorem. -/
theorem isWeakTorsion_of_global_smooth_test_equation {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane}
    (hD : IsOpen D) (hb : Bornology.IsBounded D) (hu : MemH10 D u g)
    (htest : ∀ ψ : Plane → ℝ, IsTest D ψ →
      (∫ x, inner (𝕜 := ℝ) (g x) (gradient ψ x)) = ∫ x, ψ x) :
    IsWeakTorsion D u g := by
  let S := HilbertDirichlet.solutionOn D hD.measurableSet hb
  have hs := S.weakEquation
  have hdiff := hu.sub hs.1
  have hharm : IsWeakHarmonicOn D (fun x => u x - S.value x)
      (fun x => g x - S.weakGradient x) := by
    refine ⟨hdiff.distributionalGradient, ?_⟩
    intro ψ hψ
    have hgint := integrable_real_inner_of_memLp_two hu.2.1 (hψ.memLp_gradient (p := 2))
    have hsint := integrable_real_inner_of_memLp_two hs.1.2.1 (hψ.memLp_gradient (p := 2))
    simp only [inner_sub_left]
    rw [integral_sub hgint hsint, htest ψ hψ, hs.global_smooth_test_equation hψ, sub_self]
  refine ⟨hu, ?_⟩
  intro v h hv
  have heq := hharm.sobolev_test_equation hdiff.2.1 hv
  have hgint := integrable_real_inner_of_memLp_two hu.2.1 hv.2.1
  have hsint := integrable_real_inner_of_memLp_two hs.1.2.1 hv.2.1
  simp only [inner_sub_left] at heq
  rw [integral_sub hgint hsint] at heq
  have hhz : ∀ᵐ x ∂volume, x ∉ D → h x = 0 :=
    (ae_restrict_iff' hD.measurableSet.compl).mp hv.gradient_ae_zero_off
  have hglobal (k : Plane → Plane) : (∫ x in D, inner (𝕜 := ℝ) (k x) (h x)) =
      ∫ x, inner (𝕜 := ℝ) (k x) (h x) := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hhz] with x hx hnot
    simp [hx hnot]
  calc
    _ = ∫ x, inner (𝕜 := ℝ) (g x) (h x) := hglobal g
    _ = ∫ x, inner (𝕜 := ℝ) (S.weakGradient x) (h x) := sub_eq_zero.mp heq
    _ = ∫ x in D, inner (𝕜 := ℝ) (S.weakGradient x) (h x) := (hglobal _).symm
    _ = ∫ x in D, v x := hs.2 v h hv

/-- Actual classical Poisson data in the concrete H¹₀ graph give the full
weak torsion equation.  The local smoothness, a.e. gradient identification
and classical Laplacian are the only analytic inputs; no test equation or
boundary trace characterization is presumed. -/
theorem isWeakTorsion_of_classical_poisson {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane}
    (hD : IsOpen D) (hb : Bornology.IsBounded D) (hu : MemH10 D u g)
    (hsmooth : ContDiffOn ℝ ∞ u D)
    (hgrad : g =ᵐ[volume.restrict D] gradient u)
    (hlap : ∀ x ∈ D, WeakHarmonicRegularity.planarLaplacian u x = -1) :
    IsWeakTorsion D u g := by
  apply isWeakTorsion_of_global_smooth_test_equation hD hb hu
  intro ψ hψ
  have hg : ∀ᵐ x ∂volume, x ∈ D → g x = gradient u x :=
    (ae_restrict_iff' hD.measurableSet).mp hgrad
  calc
    _ = ∫ x, inner (𝕜 := ℝ) (gradient u x) (gradient ψ x) := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      by_cases hxD : x ∈ D
      · rw [hx hxD]
      · simp only [gradient_eq_zero_of_not_mem_tsupport (fun h => hxD (hψ.2.2 h)),
          inner_zero_right]
    _ = ∫ x, ψ x := classical_poisson_smooth_test_equation hD hsmooth hlap hψ

end Torsion

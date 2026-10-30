module

public import Torsion.ClassicalWeakTorsion

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Compact-test integration by parts for actual locally smooth functions

A genuine compact smooth cutoff localizes the gradient. The identities hold
on arbitrary open sets and require neither boundary regularity nor global
Sobolev membership of the locally smooth function.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion

private theorem continuous_directional {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : Plane) : Continuous (fun x => fderiv ℝ f x v) :=
  (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp (hf.continuous_fderiv (by simp))

/-- Classical Laplacians give the full-plane smooth-test identity after
actual compact localization. -/
theorem classical_laplacian_smooth_test_equation {D : Set Plane} {u ψ : Plane → ℝ}
    (hD : IsOpen D) (hu : ContDiffOn ℝ ∞ u D)
    (hψ : IsTest D ψ) :
    (∫ x, inner (𝕜 := ℝ) (gradient u x) (gradient ψ x)) =
      -(∫ x, WeakHarmonicRegularity.planarLaplacian u x * ψ x) := by
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
      simp [f₁, f₂, G, hy, fderiv_apply_eq_inner_gradient, Complex.inner, Complex.mul_re]
      ring
    · simp [fderiv_apply_eq_inner_gradient, gradient_eq_zero_of_not_mem_tsupport hx]
  have hrightPoint (x : Plane) :
      fderiv ℝ f₁ x (1 : Plane) * ψ x + fderiv ℝ f₂ x Complex.I * ψ x =
        WeakHarmonicRegularity.planarLaplacian u x * ψ x := by
    by_cases hx : x ∈ tsupport ψ
    · rw [hlocal₁ hx, hlocal₂ hx]
      change _ = ((fderiv ℝ G x 1).re + (fderiv ℝ G x Complex.I).im) * ψ x
      ring
    · simp [image_eq_zero_of_nmem_tsupport hx]
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
      (∫ x, fderiv ℝ f₂ x Complex.I * ψ x) = (∫ x, WeakHarmonicRegularity.planarLaplacian u x * ψ x) := by
    rw [← integral_add hR₁ hR₂]
    simp_rw [hrightPoint]
  calc
    _ = ∫ x, f₁ x * fderiv ℝ ψ x (1 : Plane) + f₂ x * fderiv ℝ ψ x Complex.I :=
      integral_congr_ae (ae_of_all _ hleftPoint)
    _ = (∫ x, f₁ x * fderiv ℝ ψ x (1 : Plane)) +
        (∫ x, f₂ x * fderiv ℝ ψ x Complex.I) := integral_add hL₁ hL₂
    _ = -(∫ x, WeakHarmonicRegularity.planarLaplacian u x * ψ x) := by linarith

/-- Local smoothness is sufficient for integrability of every compact-test
gradient pairing, including on unbounded open regions. -/
theorem classical_smooth_test_pairing_integrable {D : Set Plane} {u ψ : Plane → ℝ}
    (hD : IsOpen D) (hu : ContDiffOn ℝ ∞ u D) (hψ : IsTest D ψ) :
    Integrable (fun x => inner (𝕜 := ℝ) (gradient u x) (gradient ψ x)) := by
  obtain ⟨η, hη, hone⟩ := exists_test_eq_one_near_compact hD hψ.2.1 hψ.2.2
  have hf := hη.mul_contDiffOn hD hu
  apply (integrable_real_inner_of_memLp_two (hf.memLp_gradient (p := 2))
    (hψ.memLp_gradient (p := 2))).congr
  apply ae_of_all
  intro x
  by_cases hx : x ∈ tsupport ψ
  · have hηone : η =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) :=
      hone.filter_mono (nhds_le_nhdsSet hx)
    have heq : (fun y => η y * u y) =ᶠ[𝓝 x] u := by
      filter_upwards [hηone] with y hy
      simp [hy]
    dsimp only
    rw [heq.gradient_eq]
  · simp [gradient_eq_zero_of_not_mem_tsupport hx]

/-- Actual classically harmonic functions annihilate compact smooth tests
under the genuine weak gradient pairing. -/
theorem classical_harmonic_smooth_test_equation {D : Set Plane} {u ψ : Plane → ℝ}
    (hD : IsOpen D) (hu : ContDiffOn ℝ ∞ u D)
    (hlap : ∀ x ∈ D, WeakHarmonicRegularity.planarLaplacian u x = 0)
    (hψ : IsTest D ψ) :
    (∫ x, inner (𝕜 := ℝ) (gradient u x) (gradient ψ x)) = 0 := by
  rw [classical_laplacian_smooth_test_equation hD hu hψ]
  have heq (x : Plane) : WeakHarmonicRegularity.planarLaplacian u x * ψ x = 0 := by
    by_cases hx : x ∈ D
    · rw [hlap x hx, zero_mul]
    · rw [image_eq_zero_of_nmem_tsupport (fun h => hx (hψ.2.2 h)), mul_zero]
  simp_rw [heq]
  simp

/-- The same harmonic identity on the actual open region, with its restricted
Lebesgue measure. The test gradient vanishes everywhere outside the region. -/
theorem classical_harmonic_set_smooth_test_equation {D : Set Plane} {u ψ : Plane → ℝ}
    (hD : IsOpen D) (hu : ContDiffOn ℝ ∞ u D)
    (hlap : ∀ x ∈ D, WeakHarmonicRegularity.planarLaplacian u x = 0)
    (hψ : IsTest D ψ) :
    (∫ x in D, inner (𝕜 := ℝ) (gradient u x) (gradient ψ x)) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact classical_harmonic_smooth_test_equation hD hu hlap hψ
  · intro x hx
    rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hx (hψ.2.2 h)), inner_zero_right]

end Torsion

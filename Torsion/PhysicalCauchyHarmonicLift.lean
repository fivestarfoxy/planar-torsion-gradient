import Torsion.PhysicalCauchyGreenNormal
import Torsion.CauchyTransformBoundaryExtension

/-!
# Actual harmonic lifting of compact boundary data

The lift is the imaginary part of the original real-density Cauchy integral,
composed with the actual constructed conformal inverse. Harmonicity and
arbitrary-approach boundary traces are proved for these concrete functions.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The actual physical harmonic extension of a real parameter density. -/
def physicalHarmonicLift (φ g : ℝ → ℝ) (w : Plane) : ℝ :=
  (realCauchy g (cauchyInverse φ w)).im

theorem physicalHarmonicLift_cauchy {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) (g : ℝ → ℝ)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    physicalHarmonicLift φ g (cauchy φ z) = (realCauchy g z).im := by
  simp only [physicalHarmonicLift, cauchyInverse_cauchy hφ hodd hzero hpos hz]

/-- The physical lift is the actual normalized half-plane Poisson integral
in the constructed inverse coordinate. -/
theorem physicalHarmonicLift_eq_poisson_integral {φ g : ℝ → ℝ}
    (hg : Continuous g) {w : Plane} (hw : w ∈ cauchyImage φ) :
    physicalHarmonicLift φ g w = ∫ s in Icc (-1 : ℝ) 1,
      (Real.pi⁻¹ * (cauchyInverse φ w).im /
        (((cauchyInverse φ w).re - s) ^ 2 + (cauchyInverse φ w).im ^ 2)) * g s :=
  realCauchy_im_eq_poisson hg (cauchyInverse_mem hw)

/-- Nonnegative actual boundary data produce a nonnegative physical lift. -/
theorem physicalHarmonicLift_nonneg {φ g : ℝ → ℝ}
    (hg : Continuous g) (hgpos : ∀ s ∈ Icc (-1 : ℝ) 1, 0 ≤ g s)
    {w : Plane} (hw : w ∈ cauchyImage φ) : 0 ≤ physicalHarmonicLift φ g w := by
  rw [physicalHarmonicLift_eq_poisson_integral hg hw]
  apply setIntegral_nonneg measurableSet_Icc
  intro s hs
  have him : 0 < (cauchyInverse φ w).im := cauchyInverse_mem hw
  exact mul_nonneg (by positivity) (hgpos s hs)

/-- Imaginary parts of actual holomorphic functions satisfy the classical
planar harmonic equation. -/
theorem planarLaplacian_im_eq_zero {U : Set Plane} (hU : IsOpen U)
    {B : Plane → Plane} (hB : DifferentiableOn ℂ B U)
    (hD : DifferentiableOn ℂ (deriv B) U) {w : Plane} (hw : w ∈ U) :
    WeakHarmonicRegularity.planarLaplacian (fun z => (B z).im) w = 0 := by
  have heq : gradient (fun z => (B z).im) =ᶠ[𝓝 w]
      (fun z => Complex.I * star (deriv B z)) := by
    filter_upwards [hU.mem_nhds hw] with z hz
    exact (PhysicalTorsion.hasGradientAt_im_of_hasDerivAt
      (hB.differentiableAt (hU.mem_nhds hz)).hasDerivAt).gradient
  have hd := ((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp w
    (hD.differentiableAt (hU.mem_nhds hw)).hasDerivAt.complexToReal_fderiv).const_mul Complex.I
  change HasFDerivAt (fun z => Complex.I * star (deriv B z)) _ w at hd
  unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
  rw [heq.fderiv_eq, hd.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.mul_re, Complex.mul_im]

theorem physicalHarmonicLift_laplacian_eq_zero {φ g : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) (hg : Continuous g)
    {w : Plane} (hw : w ∈ cauchyImage φ) :
    WeakHarmonicRegularity.planarLaplacian (physicalHarmonicLift φ g) w = 0 := by
  have hU := cauchyImage_isOpen hφ hodd hzero hpos
  have hInv := cauchyInverse_differentiableOn hφ hodd hzero hpos
  have hB : AnalyticOnNhd ℂ (realCauchy g ∘ cauchyInverse φ) (cauchyImage φ) :=
    ((realCauchy_differentiableOn hg).comp hInv (fun z hz => cauchyInverse_mem hz)).analyticOnNhd hU
  exact planarLaplacian_im_eq_zero hU hB.differentiableOn hB.deriv.differentiableOn hw

/-- The finite boundary trace in Cauchy coordinates permits arbitrary
half-plane approaches and requires only continuous zero-exterior data. -/
theorem physicalHarmonicLift_cauchy_boundary_tendsto {φ g : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hg : Continuous g) (hgzero : ∀ s : ℝ, 1 ≤ |s| → g s = 0) (t : ℝ) :
    Tendsto (fun z => physicalHarmonicLift φ g (cauchy φ z))
      (𝓝[upperHalfPlane] (t : Plane)) (𝓝 (g t)) := by
  apply (realCauchy_im_boundary_tendsto hg hgzero t).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (physicalHarmonicLift_cauchy hφ hodd hzero hpos g hz).symm

/-- The same trace holds along arbitrary physical interior approaches to
every finite boundary point, including both free/flat junctions. -/
theorem physicalHarmonicLift_boundary_tendsto {φ g : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hg : Continuous g) (hgzero : ∀ s : ℝ, 1 ≤ |s| → g s = 0) (t : ℝ) :
    Tendsto (physicalHarmonicLift φ g)
      (𝓝[cauchyImage φ] (cauchyExtension φ (t : Plane))) (𝓝 (g t)) := by
  have hInv := cauchyInverse_boundary_tendsto hφ hα0 hα1 hodd hzero hpos t
  have hInvH : Tendsto (cauchyInverse φ)
      (𝓝[cauchyImage φ] (cauchyExtension φ (t : Plane)))
      (𝓝[upperHalfPlane] (t : Plane)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hInv, by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact cauchyInverse_mem hw⟩
  exact (realCauchy_im_boundary_tendsto hg hgzero t).comp hInvH

end Torsion.Spectral

import Torsion.PhysicalTorsionCalculus
import Torsion.CauchyConformalGeometry.Inverse
import Torsion.CauchySpectralIdentity
import Mathlib.Analysis.Complex.ReImTopology

/-!
# The physical Cauchy candidate on its actual conformal image

The inverse and physical holomorphic function are constructed. The classical
Poisson equation, physical derivative identity, and zero boundary limits in
the conformal parameter are proved. Identifying this candidate as H¹₀ weak
torsion still requires boundary admissibility; no such membership is assumed
or asserted here.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The physical holomorphic function `A ∘ F⁻¹` on the actual image. -/
def physicalHolomorphic (φ : ℝ → ℝ) : Plane → Plane :=
  auxiliary φ ∘ cauchyInverse φ

/-- The physical scalar candidate in (7.1), now with an actual constructed
inverse instead of an assumed conformal map. -/
def physicalCandidate (φ : ℝ → ℝ) : Plane → ℝ :=
  PhysicalTorsion.candidate (physicalHolomorphic φ)

theorem physicalHolomorphic_cauchy {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    physicalHolomorphic φ (cauchy φ z) = auxiliary φ z := by
  simp only [physicalHolomorphic, Function.comp_apply,
    cauchyInverse_cauchy hφ hodd hzero hpos hz]

/-- Holomorphy is proved by composition with the constructed analytic
inverse on the actual open image. -/
theorem physicalHolomorphic_analyticOnNhd {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    AnalyticOnNhd ℂ (physicalHolomorphic φ) (cauchyImage φ) :=
  (auxiliary_analyticOnNhd hφ.continuousOn).comp
    (cauchyInverse_analyticOnNhd hφ hodd hzero hpos)
    (fun _ hw => cauchyInverse_mem hw)

/-- The chain rule through the actual inverse justifies division by F'. -/
theorem physicalHolomorphic_hasDerivAt {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    HasDerivAt (physicalHolomorphic φ)
      (deriv (auxiliary φ) z / deriv (cauchy φ) z) (cauchy φ z) := by
  have hA := (auxiliary_analyticOnNhd hφ.continuousOn z hz).differentiableAt.hasDerivAt
  have hA' : HasDerivAt (auxiliary φ) (deriv (auxiliary φ) z)
      (cauchyInverse φ (cauchy φ z)) := by
    simpa only [cauchyInverse_cauchy hφ hodd hzero hpos hz] using hA
  simpa only [physicalHolomorphic, div_eq_mul_inv] using
    hA'.comp (cauchy φ z) (cauchyInverse_hasDerivAt hφ hodd hzero hpos hz)

/-- The physical candidate satisfies -ΔU=1 on its actual conformal image.
This assertion is a classical PDE statement, with H¹₀ identification left
separate and explicit. -/
theorem physicalCandidate_laplacian_eq_neg_one {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ cauchyImage φ) :
    WeakHarmonicRegularity.planarLaplacian (physicalCandidate φ) w = -1 := by
  have hB := physicalHolomorphic_analyticOnNhd hφ hodd hzero hpos
  exact PhysicalTorsion.candidate_laplacian_eq_neg_one
    (cauchyImage_isOpen hφ hodd hzero hpos) hB.differentiableOn hB.deriv.differentiableOn hw

/-- Formula (7.4) follows from the actual nonlinear identity, itself now
proved from the concrete linear Hilbert boundary equation. -/
theorem deriv_physicalHolomorphic_of_holder_boundary_equation
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    deriv (physicalHolomorphic φ) (cauchy φ z) =
      ComplexIdentity.physicalDerivative a b (deriv (cauchy φ) z) := by
  rw [(physicalHolomorphic_hasDerivAt (hφ.continuous hα0) hodd hzero hpos hz).deriv]
  exact ComplexIdentity.quotient_identity a b _ _
    (cauchy_derivative_ne_zero (hφ.continuous hα0) hodd hzero hpos hz)
    (quadratic_identity_of_holder_boundary_equation ha hφ hα0 hα1 hodd hzero hlinear z hz)

/-- The exact physical gradient throughout the conformal image, derived
from the actual inverse, classical gradient and quadratic identity. -/
theorem gradient_physicalCandidate_cauchy {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    gradient (physicalCandidate φ) (cauchy φ z) =
      Complex.I * star (ComplexIdentity.physicalDerivative a b (deriv (cauchy φ) z)) -
        ((cauchy φ z).im : ℂ) * Complex.I := by
  have hB := (physicalHolomorphic_analyticOnNhd (hφ.continuous hα0) hodd hzero hpos)
    (cauchy φ z) ⟨z, hz, rfl⟩
  rw [physicalCandidate, PhysicalTorsion.gradient_candidate hB.differentiableAt]
  simp only [PhysicalTorsion.candidateGradient,
    deriv_physicalHolomorphic_of_holder_boundary_equation ha hφ hα0 hα1 hodd hzero hpos
      hlinear hz]

private theorem real_mem_closure_upperHalfPlane (x : ℝ) :
    (x : Plane) ∈ closure upperHalfPlane := by
  rw [upperHalfPlane, Complex.closure_setOf_lt_im]
  simp

/-- Zero boundary values are proved as actual arbitrary-approach limits in
the conformal parameter. No identification of the physical boundary or its
trace space is hidden in the statement. -/
theorem physicalCandidate_cauchy_boundary_tendsto_zero {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) (x : ℝ) :
    Tendsto (fun z => physicalCandidate φ (cauchy φ z))
      (𝓝[upperHalfPlane] (x : Plane)) (𝓝 0) := by
  have hcont := hφ.continuous hα0
  obtain ⟨hF, _, hA, _⟩ := cauchy_extensions_diffContOnCl_of_holder
    hφ hα0 hα1 hodd hzero
  have hV : ContinuousOn (fun z => -((cauchyExtension φ z).im) ^ 2 / 2 +
      (auxiliaryExtension φ z).im) (closure upperHalfPlane) :=
    (((Complex.continuous_im.comp_continuousOn hF.continuousOn).pow 2).neg.div_const 2).add
      (Complex.continuous_im.comp_continuousOn hA.continuousOn)
  have hlim := (hV (x : Plane) (real_mem_closure_upperHalfPlane x)).mono subset_closure
  have hzeroV : -((cauchyExtension φ (x : Plane)).im) ^ 2 / 2 +
      (auxiliaryExtension φ (x : Plane)).im = 0 := by
    simp [cauchyExtension_ofReal, auxiliaryExtension_ofReal, pow_two,
      Complex.mul_re, Complex.mul_im]
    ring
  change Tendsto (fun z => -((cauchyExtension φ z).im) ^ 2 / 2 +
    (auxiliaryExtension φ z).im) (𝓝[upperHalfPlane] (x : Plane))
      (𝓝 (-((cauchyExtension φ (x : Plane)).im) ^ 2 / 2 +
        (auxiliaryExtension φ (x : Plane)).im)) at hlim
  rw [hzeroV] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [cauchyExtension_eq hcont.continuousOn hz,
    auxiliaryExtension_eq hcont.continuousOn hz]
  simp only [physicalCandidate, PhysicalTorsion.candidate,
    physicalHolomorphic_cauchy hcont hodd hzero hpos hz]

end Torsion.Spectral

module

public import Torsion.PhysicalCauchyBoundary

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A harmonic marked-kernel candidate and the constant free-arc product

The scalar function here is the concrete `Im(F⁻¹)/M` from equation (19).
Its positivity, harmonicity and differential formula are proved on the
actual Cauchy image.  Its free-arc gradient limits yield the stationarity
product with the actual torsion-candidate gradient.  Identification with a
Green-function Poisson kernel, and a global calibration, are separate
results and are not asserted here.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The explicit physical marked-kernel candidate in equation (19).
No Green-function representation is included in this definition. -/
def physicalMarkedKernel (φ : ℝ → ℝ) (w : Plane) : ℝ :=
  (cauchyInverse φ w).im / mass φ

/-- The explicit kernel has the prescribed half-plane pullback. -/
theorem physicalMarkedKernel_cauchy {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    physicalMarkedKernel φ (cauchy φ z) = z.im / mass φ := by
  simp only [physicalMarkedKernel, cauchyInverse_cauchy hφ hodd hzero hpos hz]

/-- The actual scalar function is strictly positive throughout the image. -/
theorem physicalMarkedKernel_pos {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ cauchyImage φ) :
    0 < physicalMarkedKernel φ w :=
  div_pos (cauchyInverse_mem hw) (mass_pos hφ hpos)

private theorem hasGradientAt_im_div {B : Plane → Plane} {d w : Plane} (M : ℝ)
    (hB : HasDerivAt B d w) :
    HasGradientAt (fun z => (B z).im / M)
      (M⁻¹ • (Complex.I * star d)) w := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have h := (hasGradientAt_iff_hasFDerivAt.mp
    (PhysicalTorsion.hasGradientAt_im_of_hasDerivAt hB)).mul_const M⁻¹
  convert h using 1
  simp only [map_smul]

/-- Differentiation through the actual conformal inverse gives the physical
kernel gradient; the reciprocal is justified by proved univalence. -/
theorem physicalMarkedKernel_hasGradientAt_cauchy {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    HasGradientAt (physicalMarkedKernel φ)
      ((mass φ)⁻¹ • (Complex.I * star (deriv (cauchy φ) z)⁻¹)) (cauchy φ z) :=
  hasGradientAt_im_div (mass φ) (cauchyInverse_hasDerivAt hφ hodd hzero hpos hz)

theorem gradient_physicalMarkedKernel_cauchy {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    gradient (physicalMarkedKernel φ) (cauchy φ z) =
      (mass φ)⁻¹ • (Complex.I * star (deriv (cauchy φ) z)⁻¹) :=
  (physicalMarkedKernel_hasGradientAt_cauchy hφ hodd hzero hpos hz).gradient

private theorem divergence_im_div_gradient {B : Plane → Plane} {w : Plane} (M : ℝ)
    (hD : DifferentiableAt ℂ (deriv B) w) :
    WeakHarmonicRegularity.planarDivergence
      (fun z => M⁻¹ • (Complex.I * star (deriv B z))) w = 0 := by
  have h := (((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp w
    hD.hasDerivAt.complexToReal_fderiv).const_mul Complex.I).const_smul M⁻¹
  change HasFDerivAt (fun z => M⁻¹ • (Complex.I * star (deriv B z))) _ w at h
  unfold WeakHarmonicRegularity.planarDivergence
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.mul_re, Complex.mul_im]

/-- The constructed marked-kernel candidate is actually classically harmonic
on the actual conformal image. -/
theorem physicalMarkedKernel_laplacian_eq_zero {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ cauchyImage φ) :
    WeakHarmonicRegularity.planarLaplacian (physicalMarkedKernel φ) w = 0 := by
  have hU := cauchyImage_isOpen hφ hodd hzero hpos
  have hB := cauchyInverse_analyticOnNhd hφ hodd hzero hpos
  have heq : gradient (physicalMarkedKernel φ) =ᶠ[𝓝 w]
      (fun z => (mass φ)⁻¹ • (Complex.I * star (deriv (cauchyInverse φ) z))) := by
    filter_upwards [hU.mem_nhds hw] with z hz
    exact (hasGradientAt_im_div (mass φ) (hB z hz).differentiableAt.hasDerivAt).gradient
  unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
  rw [heq.fderiv_eq]
  exact divergence_im_div_gradient (mass φ) (hB.deriv w hw).differentiableAt

/-- At every finite real parameter the actual kernel tends to zero along
arbitrary approaches from the half-plane. -/
theorem physicalMarkedKernel_cauchy_boundary_tendsto_zero {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) (x : ℝ) :
    Tendsto (fun z => physicalMarkedKernel φ (cauchy φ z))
      (𝓝[upperHalfPlane] (x : Plane)) (𝓝 0) := by
  have h : Tendsto (fun z : Plane => z.im / mass φ)
      (𝓝[upperHalfPlane] (x : Plane)) (𝓝 0) := by
    simpa using ((Complex.continuous_im.tendsto (x : Plane)).mono_left nhdsWithin_le_nhds).div_const (mass φ)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (physicalMarkedKernel_cauchy hφ hodd hzero hpos hz).symm

/-- The actual physical kernel-gradient limit exists at every point of the
closed free arc, including both junctions. -/
theorem gradient_physicalMarkedKernel_cauchy_boundary_tendsto
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun z => gradient (physicalMarkedKernel φ) (cauchy φ z))
      (𝓝[upperHalfPlane] (x : Plane))
      (𝓝 ((mass φ)⁻¹ •
        (Complex.I * star (cauchyDerivativeExtension φ (x : Plane))⁻¹))) := by
  have hne := cauchyDerivativeExtension_ne_zero_on_interval
    ha hφ hα0 hα1 hodd hzero hpos hlinear hx
  have hxcl : (x : Plane) ∈ closure upperHalfPlane := by
    simp [upperHalfPlane, Complex.closure_setOf_lt_im]
  have hlim := ((cauchyDerivativeExtension_diffContOnCl hφ hα0 hzero).continuousOn
    (x : Plane) hxcl).mono subset_closure
  have h := (((continuous_star.tendsto _).comp (hlim.inv₀ hne)).const_mul Complex.I).const_smul
    ((mass φ)⁻¹ : ℝ)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [gradient_physicalMarkedKernel_cauchy (hφ.continuous hα0) hodd hzero hpos hz]
  simp only [Function.comp_apply,
    cauchyDerivativeExtension_eq (hφ.continuous hα0) hodd hzero hz]

/-- The norm of the boundary kernel gradient is the reciprocal boundary
speed divided by the actual height mass. -/
theorem norm_gradient_physicalMarkedKernel_cauchy_boundary_tendsto
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun z => ‖gradient (physicalMarkedKernel φ) (cauchy φ z)‖)
      (𝓝[upperHalfPlane] (x : Plane))
      (𝓝 (1 / (mass φ * ‖cauchyDerivativeExtension φ (x : Plane)‖))) := by
  have hM := mass_pos (hφ.continuous hα0).continuousOn hpos
  have h := (gradient_physicalMarkedKernel_cauchy_boundary_tendsto
    ha hφ hα0 hα1 hodd hzero hpos hlinear hx).norm
  simpa [norm_smul, norm_mul, norm_inv, Complex.norm_I, norm_star,
    Real.norm_eq_abs, abs_of_pos hM, mul_inv, one_div, mul_comm] using h

/-- The product of actual torsion-candidate and kernel-gradient norms has
the same free-arc limit everywhere, namely `1/(2aM)`. This is the local
stationarity factor, without asserting the global calibration inequality. -/
theorem gradient_product_physicalCandidate_kernel_boundary_tendsto
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun z => ‖gradient (physicalCandidate φ) (cauchy φ z)‖ *
      ‖gradient (physicalMarkedKernel φ) (cauchy φ z)‖)
      (𝓝[upperHalfPlane] (x : Plane)) (𝓝 (1 / (2 * a * mass φ))) := by
  have h := (norm_gradient_physicalCandidate_cauchy_boundary_tendsto
    ha hφ hα0 hα1 hodd hzero hpos hlinear hx).mul
    (norm_gradient_physicalMarkedKernel_cauchy_boundary_tendsto
      ha hφ hα0 hα1 hodd hzero hpos hlinear hx)
  have hM := (mass_pos (hφ.continuous hα0).continuousOn hpos).ne'
  have hD := norm_ne_zero_iff.mpr (cauchyDerivativeExtension_ne_zero_on_interval
    ha hφ hα0 hα1 hodd hzero hpos hlinear hx)
  convert h using 1
  field_simp [hM, hD, ha.ne']
  ring

end Torsion.Spectral

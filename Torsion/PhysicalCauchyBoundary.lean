import Torsion.PhysicalCauchyTorsion

/-!
# Boundary and infinity limits of the actual physical Cauchy gradient

These are actual limits for the classical candidate on the constructed
conformal image.  They do not identify that candidate with weak H¹₀ torsion,
nor do they silently identify a physical outward normal before the boundary
geometry has been proved.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace Torsion.Spectral

/-- A continuous conformal-parameter extension of the explicit physical
gradient.  Its equality with the actual gradient in H is proved below. -/
def physicalGradientExtension (a b : ℝ) (φ : ℝ → ℝ) (z : Plane) : Plane :=
  Complex.I * star (ComplexIdentity.physicalDerivative a b
    (cauchyDerivativeExtension φ z)) - ((cauchyExtension φ z).im : ℂ) * Complex.I

/-- The gradient expression has a genuine continuous closed-half-plane
extension, constructed from the actual Cauchy extensions. -/
theorem physicalGradientExtension_continuousOn {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    ContinuousOn (physicalGradientExtension a b φ) (closure upperHalfPlane) := by
  obtain ⟨hF, hD, _, _⟩ := cauchy_extensions_diffContOnCl_of_holder
    hφ hα0 hα1 hodd hzero
  have hp : ContinuousOn (fun z => ComplexIdentity.physicalDerivative a b
      (cauchyDerivativeExtension φ z)) (closure upperHalfPlane) :=
    continuousOn_const.sub (hD.continuousOn.div_const _)
  exact (continuousOn_const.mul (continuous_star.comp_continuousOn hp)).sub
    ((Complex.continuous_ofReal.comp_continuousOn
      (Complex.continuous_im.comp_continuousOn hF.continuousOn)).mul continuousOn_const)

/-- On the interior this constructed extension is the actual classical
gradient, using the proved physical derivative identity. -/
theorem physicalGradientExtension_eq_gradient {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    physicalGradientExtension a b φ z = gradient (physicalCandidate φ) (cauchy φ z) := by
  rw [gradient_physicalCandidate_cauchy ha hφ hα0 hα1 hodd hzero hpos hlinear hz]
  simp only [physicalGradientExtension,
    cauchyDerivativeExtension_eq (hφ.continuous hα0) hodd hzero hz,
    cauchyExtension_eq (hφ.continuous hα0).continuousOn hz]

private theorem rotated_gradient_boundary_algebra {a b Y : ℝ} {D : ℂ}
    (ha : a ≠ 0) (hv : D.re = b - a * Y) :
    Complex.I * star (ComplexIdentity.physicalDerivative a b D) - (Y : ℂ) * Complex.I =
      Complex.I * D / ((2 * a : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [ComplexIdentity.physicalDerivative, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
  · field_simp [ha]
  · rw [hv]
    field_simp [ha]
    ring

/-- At every point of the closed free arc, the limiting physical gradient
is the positively rotated parameter tangent divided by `2a`.  Endpoints and
the central point are included. -/
theorem physicalGradientExtension_ofReal {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    physicalGradientExtension a b φ (x : Plane) =
      Complex.I * cauchyDerivativeExtension φ (x : Plane) / ((2 * a : ℝ) : ℂ) := by
  have hv := cauchyDerivativeExtension_re_eq_boundaryVelocity hφ hα0 hzero hlinear x hx
  simp only [boundaryVelocity] at hv
  simp only [physicalGradientExtension, cauchyExtension_ofReal, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, zero_mul, add_zero, zero_add]
  exact rotated_gradient_boundary_algebra ha hv

/-- Arbitrary interior approach to a finite free-arc parameter point gives
the exact physical gradient limit. -/
theorem gradient_physicalCandidate_cauchy_boundary_tendsto
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun z => gradient (physicalCandidate φ) (cauchy φ z))
      (𝓝[upperHalfPlane] (x : Plane))
      (𝓝 (Complex.I * cauchyDerivativeExtension φ (x : Plane) / ((2 * a : ℝ) : ℂ))) := by
  have hxcl : (x : Plane) ∈ closure upperHalfPlane := by
    simp [upperHalfPlane, Complex.closure_setOf_lt_im]
  have hlim := ((physicalGradientExtension_continuousOn (a := a) (b := b) hφ hα0 hα1 hodd hzero)
    (x : Plane) hxcl).mono subset_closure
  change Tendsto (physicalGradientExtension a b φ) (𝓝[upperHalfPlane] (x : Plane))
    (𝓝 (physicalGradientExtension a b φ (x : Plane))) at hlim
  rw [physicalGradientExtension_ofReal ha hφ hα0 hzero hlinear hx] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact physicalGradientExtension_eq_gradient ha hφ hα0 hα1 hodd hzero hpos hlinear hz

/-- The norm limit is the exact boundary speed divided by `2a`.
This is a classical-candidate limit; identification as torsion flux is a
separate weak-admissibility and boundary-normal theorem. -/
theorem norm_gradient_physicalCandidate_cauchy_boundary_tendsto
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun z => ‖gradient (physicalCandidate φ) (cauchy φ z)‖)
      (𝓝[upperHalfPlane] (x : Plane))
      (𝓝 (‖cauchyDerivativeExtension φ (x : Plane)‖ / (2 * a))) := by
  have h := (gradient_physicalCandidate_cauchy_boundary_tendsto
    ha.ne' hφ hα0 hα1 hodd hzero hpos hlinear hx).norm
  simpa only [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos ha] using h

/-- At the infinite conformal parameter the actual physical candidate
gradient tends to the vector `(b/a) I`, in every escape direction within H. -/
theorem gradient_physicalCandidate_cauchy_tendsto_at_infinity
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {ι : Type*} {l : Filter ι} {z : ι → Plane}
    (hz : Tendsto (fun i => ‖z i‖) l atTop) (hH : ∀ᶠ i in l, z i ∈ upperHalfPlane) :
    Tendsto (fun i => gradient (physicalCandidate φ) (cauchy φ (z i))) l
      (𝓝 (((b / a : ℝ) : ℂ) * Complex.I)) := by
  have hcont : ContinuousOn φ (Icc (0 : ℝ) 1) := (hφ.continuous hα0).continuousOn
  have hF0 := cauchy_tendsto_zero hcont hz
  have hD0 := cauchy_derivative_tendsto_zero hcont hz hH
  have hP : Tendsto (fun i => ComplexIdentity.physicalDerivative a b
      (deriv (cauchy φ) (z i))) l (𝓝 ((b / a : ℝ) : ℂ)) := by
    simpa only [ComplexIdentity.physicalDerivative, zero_div, sub_zero] using
      (tendsto_const_nhds.sub (hD0.div_const ((2 * a : ℝ) : ℂ)))
  have hstar := (continuous_star.tendsto ((b / a : ℝ) : ℂ)).comp hP
  have hFi := (Complex.continuous_im.tendsto 0).comp hF0
  have hFic := (Complex.continuous_ofReal.tendsto 0).comp hFi
  have hlim := (hstar.const_mul Complex.I).sub (hFic.mul_const Complex.I)
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_zero, zero_mul,
    sub_zero] at hlim
  have hcomm : Complex.I * ((b / a : ℝ) : ℂ) = ((b / a : ℝ) : ℂ) * Complex.I := mul_comm _ _
  rw [hcomm] at hlim
  apply hlim.congr'
  filter_upwards [hH] with i hi
  exact (gradient_physicalCandidate_cauchy ha hφ hα0 hα1 hodd hzero hpos hlinear hi).symm

/-- The corresponding gradient norm limit is the positive scalar `b/a`;
positivity of `b` is derived from the actual spectral moment identity. -/
theorem norm_gradient_physicalCandidate_cauchy_tendsto_at_infinity
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {ι : Type*} {l : Filter ι} {z : ι → Plane}
    (hz : Tendsto (fun i => ‖z i‖) l atTop) (hH : ∀ᶠ i in l, z i ∈ upperHalfPlane) :
    Tendsto (fun i => ‖gradient (physicalCandidate φ) (cauchy φ (z i))‖) l
      (𝓝 (b / a)) := by
  have hb := (coefficient_pos_and_unique_velocity_zero_of_holder_boundary_equation
    ha hφ hα0 hα1 hodd hzero hpos hlinear).1
  have h := (gradient_physicalCandidate_cauchy_tendsto_at_infinity
    ha.ne' hφ hα0 hα1 hodd hzero hpos hlinear hz hH).norm
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, abs_of_pos (div_pos hb ha)] using h

/-- The actual candidate has zero value at the infinite conformal
parameter, by the proved Cauchy decay and the constructed inverse identity. -/
theorem physicalCandidate_cauchy_tendsto_zero_at_infinity
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {ι : Type*} {l : Filter ι} {z : ι → Plane}
    (hz : Tendsto (fun i => ‖z i‖) l atTop) (hH : ∀ᶠ i in l, z i ∈ upperHalfPlane) :
    Tendsto (fun i => physicalCandidate φ (cauchy φ (z i))) l (𝓝 0) := by
  have hF := (Complex.continuous_im.tendsto 0).comp (cauchy_tendsto_zero hφ.continuousOn hz)
  have hA := (Complex.continuous_im.tendsto 0).comp (auxiliary_tendsto_zero hφ.continuousOn hz)
  have hlim := ((hF.pow 2).neg.div_const (2 : ℝ)).add hA
  simp only [Complex.zero_im, zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div,
    zero_add] at hlim
  apply hlim.congr'
  filter_upwards [hH] with i hi
  simp only [physicalCandidate, PhysicalTorsion.candidate, Function.comp_apply,
    physicalHolomorphic_cauchy hφ hodd hzero hpos hi]

end Torsion.Spectral

import Torsion.CauchyTransformPoisson
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The normalized half-plane Poisson density

The normalization is established by an actual Lebesgue integral. The
infinity-coordinate source calculation fixes the factor used by the marked
kernel of the Cauchy image, independently of stationarity.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Torsion.HalfPlane

/-- The harmonic-measure density of the upper half-plane with respect to
Lebesgue measure on its real boundary. -/
def poisson (z : Plane) (x : ℝ) : ℝ :=
  z.im / (Real.pi * ((z.re - x) ^ 2 + z.im ^ 2))

theorem poisson_pos {z : Plane} (hz : 0 < z.im) (x : ℝ) :
    0 < poisson z x := by
  unfold poisson
  exact div_pos hz (mul_pos Real.pi_pos (by positivity))

theorem poisson_eq_rescaled_density {z : Plane} (hz : 0 < z.im) (x : ℝ) :
    poisson z x = z.im⁻¹ * Spectral.poissonDensity ((x - z.re) / z.im) := by
  unfold poisson Spectral.poissonDensity
  have h₁ : (z.re - x) ^ 2 + z.im ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h₂ : 1 + ((x - z.re) / z.im) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hz.ne', h₁, h₂]
  ring

/-- Exact mass one, including the factor `1/π` and the scale of the
physical real-boundary coordinate. -/
theorem integral_poisson {z : Plane} (hz : 0 < z.im) :
    (∫ x : ℝ, poisson z x) = 1 := by
  simp_rw [poisson_eq_rescaled_density hz]
  rw [integral_const_mul]
  have h := integral_sub_right_eq_self (μ := volume)
    (fun x : ℝ => Spectral.poissonDensity (x / z.im)) z.re
  rw [h, Measure.integral_comp_div, Spectral.integral_poissonDensity]
  simp [abs_of_pos hz, smul_eq_mul, hz.ne']

theorem poisson_eq_neg_im_inv (z : Plane) (x : ℝ) :
    poisson z x = -((z - (x : Plane))⁻¹).im / Real.pi := by
  simp only [poisson, Complex.inv_im, Complex.sub_im, Complex.ofReal_im,
    sub_zero, Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re]
  simp only [neg_div, neg_neg]
  rw [mul_comm Real.pi, div_mul_eq_div_div]
  simp [pow_two]

/-- The half-plane Poisson density at the origin, expressed after the
infinity-coordinate inversion. -/
theorem poisson_infinity_coordinate (z : Plane) :
    poisson (-z⁻¹) 0 = z.im / Real.pi := by
  rw [poisson_eq_neg_im_inv]
  simp

/-- The source Green function in the infinity coordinate, including its
continuous zero value at the boundary point. -/
def infinitySource (z : Plane) (t : ℝ) : ℝ :=
  (Real.log ‖1 - (t : Plane) * Complex.I * z‖ -
    Real.log ‖1 + (t : Plane) * Complex.I * z‖) / (2 * Real.pi)

@[simp] theorem infinitySource_zero (z : Plane) : infinitySource z 0 = 0 := by
  simp [infinitySource]

/-- The derivative of the normalized logarithmic kernel with its source
approaching infinity in the compactifying coordinate `s = it`. -/
theorem infinitySource_hasDerivAt_zero (z : Plane) :
    HasDerivAt (infinitySource z) (z.im / Real.pi) 0 := by
  have hm : HasDerivAt (fun t : ℝ => 1 - (t : Plane) * Complex.I * z)
      (-(Complex.I * z)) 0 := by
    convert ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const
      (Complex.I * z)).const_sub 1 using 1 <;> simp [mul_assoc]
  have hp : HasDerivAt (fun t : ℝ => 1 + (t : Plane) * Complex.I * z)
      (Complex.I * z) 0 := by
    convert ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const
      (Complex.I * z)).const_add 1 using 1 <;> simp [mul_assoc, add_comm]
  have hm' := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (hm.clog_real (by simp [Complex.slitPlane])) )
  have hp' := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (hp.clog_real (by simp [Complex.slitPlane])) )
  have h := (hm'.sub hp').div_const (2 * Real.pi)
  convert h using 1
  · funext t
    simp [infinitySource, Complex.log_re, Complex.reCLM_apply]
  · simp [Complex.mul_re, Complex.mul_im]
    ring

/-- The first-order source quotient retains the exact normalized coefficient. -/
theorem infinitySource_div_t_tendsto (z : Plane) :
    Tendsto (fun t : ℝ => infinitySource z t / t) (𝓝[≠] 0)
      (𝓝 (z.im / Real.pi)) := by
  have h := (infinitySource_hasDerivAt_zero z).tendsto_slope_zero
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

end Torsion.HalfPlane

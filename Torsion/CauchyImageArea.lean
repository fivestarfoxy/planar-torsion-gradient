module

public import Torsion.CauchyConformalGeometry.Inverse
public import Torsion.CauchyTransformImageBound
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.RingTheory.Complex
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Euclidean area as the actual Cauchy Jacobian integral

The image area is the original complex-plane Lebesgue measure. The
change-of-variables theorem applies to the proved injective Cauchy map;
its real Jacobian is the squared norm of its complex derivative. Thus its
finite Euclidean area supplies actual half-plane L² integrability of `F′`.
The evaluation of this energy by boundary moments is a separate step.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- Multiplication by a complex number has real determinant equal to its
squared complex norm. -/
theorem complex_mul_real_det (d : ℂ) :
    (d • (1 : ℂ →L[ℝ] ℂ)).det = ‖d‖ ^ 2 := by
  have heq : ((d • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ d := by
    ext z
    rfl
  calc
    _ = LinearMap.det (Algebra.lmul ℝ ℂ d) := congrArg LinearMap.det heq
    _ = ‖d‖ ^ 2 := by
      rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

/-- The actual Cauchy-map Jacobian on the half-plane. -/
theorem cauchy_real_fderiv_det {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (fderiv ℝ (cauchy φ) z).det = ‖deriv (cauchy φ) z‖ ^ 2 := by
  rw [(hasDerivAt_cauchy hφ hz).differentiableAt.hasDerivAt.complexToReal_fderiv.fderiv]
  exact complex_mul_real_det _

/-- The exact Euclidean measure of the actual image, as a nonnegative
half-plane Jacobian integral. No boundary-area identity is assumed. -/
theorem volume_cauchyImage_eq_lintegral_deriv_sq {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    volume (cauchyImage φ) =
      ∫⁻ z in upperHalfPlane, ENNReal.ofReal (‖deriv (cauchy φ) z‖ ^ 2) := by
  have hH : IsOpen upperHalfPlane := isOpen_lt continuous_const Complex.continuous_im
  have hjac := lintegral_abs_det_fderiv_eq_addHaar_image volume hH.measurableSet
    (fun z hz => (hasDerivAt_cauchy hφ.continuousOn hz).differentiableAt.hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt)
    (cauchy_injOn_upperHalfPlane hφ hodd hzero hpos)
  simpa only [complex_mul_real_det, abs_sq, cauchyImage] using hjac.symm

/-- The same change of variables gives the ordinary real-valued Euclidean
area, with its actual Lebesgue measure definition. -/
theorem area_cauchyImage_eq_integral_deriv_sq {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    (volume (cauchyImage φ)).toReal = ∫ z in upperHalfPlane, ‖deriv (cauchy φ) z‖ ^ 2 := by
  have hH : IsOpen upperHalfPlane := isOpen_lt continuous_const Complex.continuous_im
  have hjac := integral_image_eq_integral_abs_det_fderiv_smul volume hH.measurableSet
    (fun z hz => (hasDerivAt_cauchy hφ.continuousOn hz).differentiableAt.hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt)
    (cauchy_injOn_upperHalfPlane hφ hodd hzero hpos) (fun _ : ℂ => (1 : ℝ))
  simpa only [complex_mul_real_det, abs_sq, smul_eq_mul,
    mul_one, integral_const, measureReal_def, Measure.restrict_apply_univ, cauchyImage] using hjac

/-- Boundedness of the actual image forces convergence of its actual
half-plane squared-derivative integral. -/
theorem cauchy_deriv_sq_integrableOn {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    IntegrableOn (fun z => ‖deriv (cauchy φ) z‖ ^ 2) upperHalfPlane := by
  have hH : IsOpen upperHalfPlane := isOpen_lt continuous_const Complex.continuous_im
  have hjac := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hH.measurableSet
    (fun z hz => (hasDerivAt_cauchy hφ.continuousOn hz).differentiableAt.hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt)
    (cauchy_injOn_upperHalfPlane hφ hodd hzero hpos) (fun _ : ℂ => (1 : ℝ))
  have hfinite : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (cauchy φ '' upperHalfPlane) :=
    integrableOn_const.2 (.inr (volume_cauchy_image_lt_top hφ hodd hzero))
  simpa only [complex_mul_real_det, abs_sq, smul_eq_mul, mul_one]
    using hjac.mp hfinite

/-- The derivative of the concrete univalent Cauchy map belongs to actual
L² of the parameter half-plane. -/
theorem cauchy_deriv_memLp_two {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    MemLp (deriv (cauchy φ)) 2 (volume.restrict upperHalfPlane) := by
  have hm : AEStronglyMeasurable (deriv (cauchy φ)) (volume.restrict upperHalfPlane) :=
    (cauchy_analyticOnNhd hφ.continuousOn).deriv.continuousOn.aestronglyMeasurable
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  exact (memLp_two_iff_integrable_sq_norm hm).2
    (cauchy_deriv_sq_integrableOn hφ hodd hzero hpos)

end Torsion.Spectral

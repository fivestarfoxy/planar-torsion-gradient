import Torsion.CauchyShapeBoundaryData
import Torsion.CauchyRadialProfile
import Torsion.PhysicalCauchyHarmonicMarked
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The actual oriented radial Hadamard density

The negative convective boundary datum for a genuine radial boundary
velocity is identified pointwise with the actual argument Jacobian.
The concrete monotone boundary parametrization then gives the exact
normalized angular integral, with no change-of-variables assumption.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral

variable {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
variable (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
variable (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
variable (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
variable (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1, realCauchyBoundaryRe φ x = a * height φ x - b)
variable (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
variable (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)

include ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd

local notation "H" => cauchyAngleHomeomorph ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd
local notation "R" => ContinuousProfiles.extend
  (cauchyRadialProfile ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd)
local notation "Θ" => (fun t : ℝ => Complex.arg (cauchyExtension φ (t : Plane)))
local notation "Q" => (fun t : ℝ => cauchySupport a b φ t 0 /
  ‖cauchyExtension φ (t : Plane)‖ ^ 2)

theorem cauchyRadialProfile_extend_arg {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    R (Θ t) = ‖cauchyExtension φ (t : Plane)‖ := by
  let u : Icc (-1 : ℝ) 1 := ⟨t, ht⟩
  have hθ : (H u : ℝ) = Θ t := rfl
  rw [← hθ, ContinuousProfiles.extend_coe]
  change ‖cauchyExtension φ (((((H).symm (H u) : Icc (-1 : ℝ) 1) : ℝ)) : Plane)‖ = _
  rw [(H).symm_apply_apply]

theorem cauchy_boundary_arg_mem_Ioo {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    Θ t ∈ Ioo 0 Real.pi := by
  have hmono := cauchy_boundary_arg_strictMonoOn ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd
  have hend := cauchy_boundary_arg_endpoints hφ hα0 hα1 hodd hzero hpos
  constructor
  · have h := hmono (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) (Ioo_subset_Icc_self ht) ht.1
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, hend.1] using h
  · have h := hmono (Ioo_subset_Icc_self ht) (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) ht.2
    simpa only [Complex.ofReal_one, hend.2] using h

omit ha hα1 hodd hpos hc hd in
theorem cauchySupport_eq_neg_inner_position_tangent
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    cauchySupport a b φ t 0 = -inner (𝕜 := ℝ) (cauchyExtension φ (t : Plane))
      (Complex.I * cauchyDerivativeExtension φ (t : Plane)) := by
  rw [cauchy_boundary_tangent_eq hφ hα0 hzero hlinear ht, cauchySupport_eq]
  simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, one_mul, zero_sub, sub_zero, add_zero, zero_add,
    Complex.conj_re, Complex.conj_im, Complex.zero_re, Complex.zero_im]
  have hi : (cauchyExtension φ (t : Plane)).im = height φ t := by simp [cauchyExtension_ofReal]
  rw [hi]
  ring

theorem shapeBoundaryData_radial_density {V : Plane → Plane} {f : ℝ → ℝ}
    (hVrad : ∀ θ ∈ Ioo 0 Real.pi,
      V ((R θ : Plane) * Complex.exp ((θ : Plane) * Complex.I)) =
        (f θ : ℝ) • Complex.exp ((θ : Plane) * Complex.I))
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    shapeBoundaryData a φ V t =
      (1 / (2 * a)) * ((R (Θ t) * f (Θ t)) * Q t) := by
  have htcc := Ioo_subset_Icc_self ht
  have hθ := cauchy_boundary_arg_mem_Ioo ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd ht
  have hRθ := cauchyRadialProfile_extend_arg ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd htcc
  have hne := (norm_pos_iff.mpr (cauchy_boundary_ne_zero hφ hα0 hα1 hodd hzero hpos t)).ne'
  have hV := hVrad (Θ t) hθ
  rw [hRθ, Complex.norm_mul_exp_arg_mul_I] at hV
  have hV' : V (cauchyExtension φ (t : Plane)) =
      (f (Θ t) / ‖cauchyExtension φ (t : Plane)‖) • cauchyExtension φ (t : Plane) := by
    rw [hV]
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I (cauchyExtension φ (t : Plane))]
    simp only [Complex.real_smul, Complex.ofReal_div]
    field_simp [hne]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      congrArg (fun w : Plane => (f (Θ t) : Plane) * w)
        (Complex.norm_mul_exp_arg_mul_I (cauchyExtension φ (t : Plane)))
  have hdiv : Complex.I * cauchyDerivativeExtension φ (t : Plane) / ((2 * a : ℝ) : Plane) =
      ((2 * a)⁻¹ : ℝ) • (Complex.I * cauchyDerivativeExtension φ (t : Plane)) := by
    simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
    ring
  rw [shapeBoundaryData, hV', hdiv, real_inner_smul_left, real_inner_smul_right, hRθ]
  have hsupport := cauchySupport_eq_neg_inner_position_tangent hφ hα0 hzero hlinear htcc
  dsimp only
  rw [hsupport]
  field_simp [hne, ha.ne']
  ring

omit ha hlinear hc hd in
theorem cauchy_boundary_argument_jacobian_continuousOn : ContinuousOn Q (Icc (-1 : ℝ) 1) := by
  have hP := (cauchy_boundary_contDiff_one hφ hα0 hα1 hodd hzero).continuous
  have hY := height_continuous (hφ.continuous hα0).continuousOn
  have hV : Continuous (boundaryVelocity a b φ) := continuous_const.sub (continuous_const.mul hY)
  have hS : Continuous (fun t : ℝ => cauchySupport a b φ t 0) := by
    simp_rw [cauchySupport_eq]
    exact ((hφ.continuous hα0).mul (continuous_const.sub (Complex.continuous_re.comp hP))).add
      (hV.mul (continuous_const.sub hY))
  exact hS.continuousOn.div (hP.norm.pow 2).continuousOn (fun t _ =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (cauchy_boundary_ne_zero hφ hα0 hα1 hodd hzero hpos t)))

/-- The exact actual radial Jacobian integral. The only change of variables
used is the proved derivative of the actual boundary argument. -/
theorem cauchy_radial_argument_integral (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in Ioo (-1 : ℝ) 1, (R (Θ t) * f (Θ t)) * Q t) =
      ∫ θ in Ioo 0 Real.pi, R θ * f θ := by
  have hθc := cauchy_boundary_arg_continuousOn hφ hα0 hα1 hodd hzero hpos
  have hQc := cauchy_boundary_argument_jacobian_continuousOn (a := a) (b := b) hφ hα0 hα1 hodd hzero hpos
  have hGc : Continuous (fun θ => R θ * f θ) := (R).continuous.mul hf
  have hsub := intervalIntegral.integral_comp_mul_deriv''
    (a := (-1 : ℝ)) (b := 1) (f := Θ) (f' := Q) (g := fun θ => R θ * f θ)
    (show ContinuousOn Θ (uIcc (-1 : ℝ) 1) by simpa using hθc)
    (fun t ht => (cauchy_boundary_arg_hasDerivAt hφ hα0 hα1 hodd hzero hpos hlinear
      (show t ∈ Ioo (-1 : ℝ) 1 by simpa using ht)).hasDerivWithinAt)
    (show ContinuousOn Q (uIcc (-1 : ℝ) 1) by simpa using hQc) hGc.continuousOn
  have hend := cauchy_boundary_arg_endpoints hφ hα0 hα1 hodd hzero hpos
  dsimp only [Function.comp_apply] at hsub
  simp only [Complex.ofReal_neg, Complex.ofReal_one] at hsub
  rw [hend.1, hend.2] at hsub
  calc
    _ = ∫ t in (-1 : ℝ)..1, (R (Θ t) * f (Θ t)) * Q t := by
      rw [intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
        ← integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioo]
    _ = ∫ θ in (0 : ℝ)..Real.pi, R θ * f θ := hsub
    _ = _ := by
      rw [intervalIntegral.integral_of_le Real.pi_pos.le,
        ← integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioo]

/-- The marked harmonic-lift action of the actual radial Eulerian boundary
datum is exactly the source Hadamard angular functional, with normalization
`1/(2aM)`. -/
theorem shapeBoundaryData_radial_integral {V : Plane → Plane} {f : ℝ → ℝ}
    (hf : Continuous f)
    (hVrad : ∀ θ ∈ Ioo 0 Real.pi,
      V ((R θ : Plane) * Complex.exp ((θ : Plane) * Complex.I)) =
        (f θ : ℝ) • Complex.exp ((θ : Plane) * Complex.I)) :
    (∫ t in Icc (-1 : ℝ) 1, shapeBoundaryData a φ V t) / mass φ =
      (1 / (2 * a * mass φ)) * ∫ θ in Ioo 0 Real.pi, R θ * f θ := by
  have hpoint := fun t ht => shapeBoundaryData_radial_density ha hφ hα0 hα1 hodd hzero hpos
    hlinear hc hd hVrad (t := t) ht
  have hint : (∫ t in Icc (-1 : ℝ) 1, shapeBoundaryData a φ V t) =
      (1 / (2 * a)) * ∫ t in Ioo (-1 : ℝ) 1, (R (Θ t) * f (Θ t)) * Q t := by
    rw [integral_Icc_eq_integral_Ioo, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    exact hpoint
  rw [hint, cauchy_radial_argument_integral ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd f hf]
  simp only [div_eq_mul_inv, one_div, mul_inv]
  ring

/-- The actual harmonic Eulerian boundary lift has exactly the localized
Hadamard angular coefficient as its physical marked normal derivative. -/
theorem shapeBoundaryData_radial_hasMarkedFlux
    (hEig : IsRestrictedEigenfunction a φ) {V : Plane → Plane} {f : ℝ → ℝ}
    (hV : ContDiff ℝ ∞ V) (hVU : tsupport V ⊆ upperHalfPlane) (hf : Continuous f)
    (hVrad : ∀ θ ∈ Ioo 0 Real.pi,
      V ((R θ : Plane) * Complex.exp ((θ : Plane) * Complex.I)) =
        (f θ : ℝ) • Complex.exp ((θ : Plane) * Complex.I)) :
    HasMarkedFlux (physicalHarmonicLift φ (shapeBoundaryData a φ V))
      ((1 / (2 * a * mass φ)) * ∫ θ in Ioo 0 Real.pi, R θ * f θ) := by
  have hg := (hEig.shapeBoundaryData_smooth_compact hφ hα0 hα1 hodd hzero hV hVU).1
  have h := physicalHarmonicLift_hasMarkedFlux (hφ.continuous hα0) hodd hzero hpos hg.continuous.continuousOn
  rw [shapeBoundaryData_radial_integral ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd hf hVrad] at h
  exact h

end Torsion.Spectral

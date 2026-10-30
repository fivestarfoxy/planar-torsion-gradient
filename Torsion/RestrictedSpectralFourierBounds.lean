import Torsion.RestrictedSpectralTranslation
import Torsion.RestrictedSpectralParseval

/-!
# Quantitative Fourier bounds for the actual restricted form

The fixed support interval gives a uniform Fourier bound and a uniform
frequency Lipschitz modulus. Actual half-energy controls the full Fourier
L² tail. These are the three inputs used for compactness of the genuine
form inclusion.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff FourierTransform

namespace Torsion.Spectral

/-- The fixed restricted support gives an elementary real L¹–L² bound. -/
theorem MemRestrictedFormDomain.integral_norm_le_two_norm {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) :
    (∫ x : ℝ, ‖f x‖) ≤ 2 * ‖hf.1.toLp f‖ := by
  have h := eLpNorm_one_le_two_of_zero_exterior hf.1 hf.2.2.1
  have hp : (2 : ℝ≥0∞) ^ (1 - 1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num)
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.1.2.ne hp) h
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat] at ht
  have hL : (∫ x : ℝ, ‖f x‖) = (eLpNorm f 1 volume).toReal := by
    simpa only [eLpNorm_one_eq_lintegral_enorm] using integral_norm_eq_lintegral_enorm hf.1.1
  have hp2 : (2 : ℝ) ^ (1 - 1 / (2 : ℝ)) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  rw [hL, Lp.norm_toLp]
  nlinarith [ENNReal.toReal_nonneg (a := eLpNorm f 2 volume)]

/-- Uniform pointwise bound of the actual Fourier transform. -/
theorem MemRestrictedFormDomain.norm_fourier_le_two_norm {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (ξ : ℝ) :
    ‖fourier f ξ‖ ≤ 2 * ‖hf.1.toLp f‖ :=
  (norm_fourier_le_integral_norm f ξ).trans hf.integral_norm_le_two_norm

/-- The elementary global Lipschitz estimate between two unit Fourier phases. -/
theorem norm_exp_real_mul_I_sub_exp_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ 2 * |a - b| := by
  have he : Complex.exp ((b : ℂ) * Complex.I) *
      Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) = Complex.exp ((a : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hd : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by rw [mul_sub, mul_one, he]
  rw [hd, norm_mul, show ‖Complex.exp ((b : ℂ) * Complex.I)‖ = 1 by simp [Complex.norm_exp], one_mul]
  exact norm_exp_real_mul_I_sub_one_le (a - b)

/-- Integrability of the actual source Fourier integrand. -/
theorem integrable_fourier_phase_mul {f : ℝ → ℝ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) := by
  apply hf.norm.mono'
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable.mul
        (Complex.ofRealCLM.integrable_comp hf).1
  · exact ae_of_all _ fun x => by simp [norm_mul, Complex.norm_exp]

/-- Common support in the restricted interval makes the actual Fourier
transform globally Lipschitz in frequency, directly from its integral. -/
theorem norm_fourier_sub_le_frequency_distance {f : ℝ → ℝ}
    (hf : Integrable f)
    (hzero : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x = 0) (ξ η : ℝ) :
    ‖fourier f ξ - fourier f η‖ ≤ (2 * (∫ x : ℝ, ‖f x‖)) * |ξ - η| := by
  unfold fourier
  rw [← integral_sub (integrable_fourier_phase_mul hf ξ) (integrable_fourier_phase_mul hf η)]
  have hbound : ∀ᵐ x : ℝ,
      ‖Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) * (f x : ℂ) -
        Complex.exp (-((x * η : ℝ) : ℂ) * Complex.I) * (f x : ℂ)‖ ≤
          (2 * |ξ - η|) * ‖f x‖ := by
    filter_upwards [hzero] with x hx
    by_cases hxI : x ∈ Ioo (-1 : ℝ) 1
    · have hxabs : |x| ≤ 1 := (abs_lt.2 hxI).le
      have hp := norm_exp_real_mul_I_sub_exp_le (-(x * ξ)) (-(x * η))
      have habs : |-(x * ξ) - -(x * η)| = |x| * |ξ - η| := by
        rw [show -(x * ξ) - -(x * η) = -(x * (ξ - η)) by ring, abs_neg, abs_mul]
      simp only [Complex.ofReal_neg, habs] at hp
      rw [← sub_mul, norm_mul, Complex.norm_real]
      have hp' : ‖Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) -
          Complex.exp (-((x * η : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * |ξ - η| := by
        exact hp.trans (by nlinarith [mul_le_mul_of_nonneg_right hxabs (abs_nonneg (ξ - η))])
      exact mul_le_mul_of_nonneg_right hp' (norm_nonneg _)
    · simp [hx hxI]
  have h := norm_integral_le_of_norm_le (hf.norm.const_mul (2 * |ξ - η|)) hbound
  rw [integral_const_mul] at h
  nlinarith

/-- The exact form-member frequency Lipschitz modulus is bounded by its
actual L² value norm. -/
theorem MemRestrictedFormDomain.norm_fourier_sub_le {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (ξ η : ℝ) :
    ‖fourier f ξ - fourier f η‖ ≤ (4 * ‖hf.1.toLp f‖) * |ξ - η| := by
  have h := norm_fourier_sub_le_frequency_distance hf.integrable hf.2.2.1 ξ η
  have hL := hf.integral_norm_le_two_norm
  have hm := mul_le_mul_of_nonneg_right hL (abs_nonneg (ξ - η))
  exact h.trans (by nlinarith)

/-- The actual half-energy gives a quantitative Fourier L² tail bound. -/
theorem fourier_tail_integral_le {f : ℝ → ℝ}
    (hf : Integrable f) (he : FiniteEnergy f) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in {ξ : ℝ | R < |ξ|}, ‖fourier f ξ‖ ^ 2) ≤
      (2 * Real.pi / R) * energy f f := by
  let S : Set ℝ := {ξ | R < |ξ|}
  have hS : MeasurableSet S := isOpen_lt continuous_const continuous_abs |>.measurableSet
  have hpoint (ξ : ℝ) (hξ : ξ ∈ S) :
      ‖fourier f ξ‖ ^ 2 ≤ R⁻¹ * (|ξ| * ‖fourier f ξ‖ ^ 2) := by
    have hh : 1 ≤ R⁻¹ * |ξ| := by
      have hh' : 1 ≤ |ξ| / R := (one_le_div hR).2 hξ.le
      simpa only [div_eq_mul_inv, mul_comm] using hh' 
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖fourier f ξ‖)]
  have htail : IntegrableOn (fun ξ : ℝ => ‖fourier f ξ‖ ^ 2) S := by
    apply ((show Integrable (fun ξ : ℝ => |ξ| * ‖fourier f ξ‖ ^ 2) volume from he).const_mul R⁻¹).integrableOn.mono'
    · exact (fourier_continuous hf).norm.pow 2 |>.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem hS] with ξ hξ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpoint ξ hξ
  have hi := setIntegral_mono_on htail
    (((show Integrable (fun ξ : ℝ => |ξ| * ‖fourier f ξ‖ ^ 2) volume from he).const_mul R⁻¹).integrableOn)
      hS hpoint
  rw [integral_const_mul] at hi
  have hwhole := setIntegral_le_integral (s := S)
    (show Integrable (fun ξ : ℝ => |ξ| * ‖fourier f ξ‖ ^ 2) volume from he)
      (ae_of_all _ fun ξ => mul_nonneg (abs_nonneg ξ) (sq_nonneg _))
  have hE : (∫ ξ : ℝ, |ξ| * ‖fourier f ξ‖ ^ 2) = (2 * Real.pi) * energy f f := by
    rw [energy_self]
    field_simp [Real.pi_ne_zero]
  calc
    _ ≤ R⁻¹ * ∫ ξ : ℝ, |ξ| * ‖fourier f ξ‖ ^ 2 :=
      hi.trans (mul_le_mul_of_nonneg_left hwhole (inv_nonneg.mpr hR.le))
    _ = _ := by rw [hE]; ring

end Torsion.Spectral

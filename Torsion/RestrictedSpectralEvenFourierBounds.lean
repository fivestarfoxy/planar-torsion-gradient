import Torsion.RestrictedSpectralFourierBounds
import Mathlib.Analysis.SpecialFunctions.Integrals
import Torsion.TrigonometricQuadraticBound
import Torsion.RestrictedSpectralCosineVariance

/-!
# Fourier caps for even restricted functions with zero mean

The constant part of the cosine kernel drops out against a zero-mean
function. Cauchy--Schwarz gives a fourth-order small-frequency cap, with
exact polynomial moment, and a uniform cap from the cosine variance.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff FourierTransform

namespace Torsion.Spectral

private theorem integral_mul_sq_le {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have heq {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    simp [hfx, hgx, RCLike.inner_apply, mul_comm]
  simpa only [heq hf hg, heq hf hf, heq hg hg, ← sq] using
    real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)

private theorem restricted_setIntegral_eq {f : ℝ → ℝ}
    (hzero : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x = 0) :
    (∫ x in Icc (-1 : ℝ) 1, f x) = ∫ x : ℝ, f x := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [hzero] with x hx hxi
  exact hx (fun h => hxi (Ioo_subset_Icc_self h))

/-- For an even real function the source Fourier transform has no sine
component. The equality uses the concrete Fourier integral. -/
theorem norm_fourier_sq_eq_cos_integral_sq_of_even {f : ℝ → ℝ}
    (hf : Integrable f) (heven : Function.Even f) (ξ : ℝ) :
    ‖fourier f ξ‖ ^ 2 = (∫ x : ℝ, Real.cos (x * ξ) * f x) ^ 2 := by
  have hp := integrable_fourier_phase_mul hf ξ
  have hre : (fourier f ξ).re = ∫ x : ℝ, Real.cos (x * ξ) * f x := by
    unfold fourier
    change RCLike.re (∫ x : ℝ, Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) = _
    rw [← integral_re hp]
    simp [Complex.exp_re]
  have hs : (∫ x : ℝ, f x * Real.sin (x * ξ)) = 0 := by
    apply integral_mul_eq_zero_of_even_odd heven
    intro x
    simp
  have him : (fourier f ξ).im = 0 := by
    unfold fourier
    change RCLike.im (∫ x : ℝ, Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) = _
    rw [← integral_im hp]
    simpa [Complex.exp_im, mul_comm, integral_neg] using congrArg Neg.neg hs
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  ring

private theorem cosine_shift_fourier_sq_le {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (heven : Function.Even f)
    (hmean : (∫ x : ℝ, f x) = 0) (ξ c : ℝ) :
    ‖fourier f ξ‖ ^ 2 ≤ (∫ x : ℝ, f x ^ 2) *
      ∫ x in Icc (-1 : ℝ) 1, (Real.cos (x * ξ) - c) ^ 2 := by
  have hgC : Continuous (fun x : ℝ => Real.cos (x * ξ) - c) := by fun_prop
  have hg : MemLp (fun x : ℝ => Real.cos (x * ξ) - c) 2
      (volume.restrict (Icc (-1 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq hgC.aestronglyMeasurable.restrict).mpr
      ((hgC.pow 2).integrableOn_Icc)
  have hzero : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 →
      f x * (Real.cos (x * ξ) - c) = 0 := by
    filter_upwards [hf.2.2.1] with x hx hxi
    rw [hx hxi, zero_mul]
  have hzeroSq : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x ^ 2 = 0 := by
    filter_upwards [hf.2.2.1] with x hx hxi
    rw [hx hxi]; norm_num
  have hprod : Integrable (fun x : ℝ => Real.cos (x * ξ) * f x) := by
    have hp := (integrable_fourier_phase_mul hf.integrable ξ).re
    simpa [Complex.exp_re] using hp
  have hshift : (∫ x : ℝ, f x * (Real.cos (x * ξ) - c)) =
      ∫ x : ℝ, Real.cos (x * ξ) * f x := by
    simp_rw [mul_sub, mul_comm (f _) (Real.cos _)]
    rw [integral_sub hprod (hf.integrable.mul_const c), integral_mul_const, hmean]
    ring
  have hCS := integral_mul_sq_le (hf.1.restrict (Icc (-1 : ℝ) 1)) hg
  rw [restricted_setIntegral_eq hzero, hshift, restricted_setIntegral_eq hzeroSq] at hCS
  rw [norm_fourier_sq_eq_cos_integral_sq_of_even hf.integrable heven]
  exact hCS

private theorem polynomial_moment :
    (∫ x in Icc (-1 : ℝ) 1, (x ^ 2 - 9 / 25) ^ 2) = 112 / 625 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have heq : (fun x : ℝ => (x ^ 2 - 9 / 25) ^ 2) =
      fun x => x ^ 4 - (18 / 25 : ℝ) * x ^ 2 + (81 / 625 : ℝ) := by funext x; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  · norm_num
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Fourth-order Fourier cap from cancellation of the constant cosine
component and the exact moment `∫(x²-9/25)² = 112/625`. -/
theorem MemRestrictedFormDomain.norm_fourier_sq_le_even_mean_zero_polynomial
    {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) (heven : Function.Even f)
    (hmean : (∫ x : ℝ, f x) = 0) (ξ : ℝ) :
    ‖fourier f ξ‖ ^ 2 ≤ (28 / 625 : ℝ) * ξ ^ 4 * (∫ x : ℝ, f x ^ 2) := by
  have hpoint (x : ℝ) : (Real.cos (x * ξ) - Real.cos ((3 / 5 : ℝ) * ξ)) ^ 2 ≤
      (ξ ^ 4 / 4) * (x ^ 2 - 9 / 25) ^ 2 := by
    have h := abs_cos_sub_cos_le_half_abs_sq_sub_sq (x * ξ) ((3 / 5 : ℝ) * ξ)
    have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at hs
    have hh : (|(x * ξ) ^ 2 - ((3 / 5 : ℝ) * ξ) ^ 2| / 2) ^ 2 =
        (ξ ^ 4 / 4) * (x ^ 2 - 9 / 25) ^ 2 := by
      rw [div_pow, sq_abs]
      ring
    rwa [hh] at hs
  have hI : (∫ x in Icc (-1 : ℝ) 1,
      (Real.cos (x * ξ) - Real.cos ((3 / 5 : ℝ) * ξ)) ^ 2) ≤
      ∫ x in Icc (-1 : ℝ) 1, (ξ ^ 4 / 4) * (x ^ 2 - 9 / 25) ^ 2 := setIntegral_mono_on
    ((by fun_prop : Continuous (fun x : ℝ =>
      (Real.cos (x * ξ) - Real.cos ((3 / 5 : ℝ) * ξ)) ^ 2)).integrableOn_Icc)
    ((by fun_prop : Continuous (fun x : ℝ =>
      (ξ ^ 4 / 4) * (x ^ 2 - 9 / 25) ^ 2)).integrableOn_Icc)
    measurableSet_Icc (fun x _ => hpoint x)
  rw [integral_const_mul, polynomial_moment] at hI
  have h := cosine_shift_fourier_sq_le hf heven hmean ξ (Real.cos ((3 / 5 : ℝ) * ξ))
  have hM : 0 ≤ ∫ x : ℝ, f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hI hM])

/-- Uniform Fourier cap from the cosine kernel's exact variance after
projection away from constants. -/
theorem MemRestrictedFormDomain.norm_fourier_sq_le_even_mean_zero_uniform
    {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) (heven : Function.Even f)
    (hmean : (∫ x : ℝ, f x) = 0) (ξ : ℝ) :
    ‖fourier f ξ‖ ^ 2 ≤ (9 / 8 : ℝ) * (∫ x : ℝ, f x ^ 2) := by
  have hM : 0 ≤ ∫ x : ℝ, f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  by_cases hξ : ξ = 0
  · have h := hf.norm_fourier_sq_le_even_mean_zero_polynomial heven hmean ξ
    rw [hξ] at h ⊢
    nlinarith
  · have h := cosine_shift_fourier_sq_le hf heven hmean ξ (Real.sin ξ / ξ)
    have hvar := mul_le_mul_of_nonneg_left (integral_cosine_variance_le hξ) hM
    exact h.trans (by nlinarith only [hvar])

end Torsion.Spectral

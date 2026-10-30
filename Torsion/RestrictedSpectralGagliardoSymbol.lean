import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The actual Gagliardo Fourier symbol, up to a positive normalization

The integrable nonnegative kernel (2-2 cos h)/h² has a strictly positive
finite integral. Real change of variables proves that its frequency-scaled
integral is exactly |ξ| times that same constant. The proof does not need
an independently evaluated sinc-squared integral.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- The one-dimensional half-derivative difference kernel in frequency. -/
def gagliardoSymbolKernel (h : ℝ) : ℝ := (2 - 2 * Real.cos h) / h ^ 2

/-- The fixed positive normalization relating the difference seminorm to
the Fourier energy. -/
def gagliardoSymbolConstant : ℝ := ∫ h : ℝ, gagliardoSymbolKernel h

theorem gagliardoSymbolKernel_nonneg (h : ℝ) : 0 ≤ gagliardoSymbolKernel h := by
  unfold gagliardoSymbolKernel
  exact div_nonneg (by linarith [Real.cos_le_one h]) (sq_nonneg h)

/-- The apparent singularity at zero has an integrable global majorant. -/
theorem gagliardoSymbolKernel_bound (h : ℝ) :
    gagliardoSymbolKernel h ≤ 5 * (1 + h ^ 2)⁻¹ := by
  have h1 : gagliardoSymbolKernel h ≤ 1 := by
    by_cases hh : h = 0
    · simp [gagliardoSymbolKernel, hh]
    · apply (div_le_one (sq_pos_of_ne_zero hh)).2
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := h)]
  have h4 : gagliardoSymbolKernel h * h ^ 2 ≤ 4 := by
    by_cases hh : h = 0
    · simp [hh]
    · rw [gagliardoSymbolKernel, div_mul_cancel₀ _ (pow_ne_zero 2 hh)]
      linarith [Real.neg_one_le_cos h]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < 1 + h ^ 2)).2
  nlinarith

theorem gagliardoSymbolKernel_integrable : Integrable gagliardoSymbolKernel := by
  have hmeas : Measurable gagliardoSymbolKernel := by
    unfold gagliardoSymbolKernel
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul (5 : ℝ)).mono' hmeas.aestronglyMeasurable
  exact ae_of_all _ fun h => by
    rw [Real.norm_eq_abs, abs_of_nonneg (gagliardoSymbolKernel_nonneg h)]
    exact gagliardoSymbolKernel_bound h

/-- The normalization is genuinely strictly positive, because the actual
kernel is positive in a neighborhood of π. -/
theorem gagliardoSymbolConstant_pos : 0 < gagliardoSymbolConstant := by
  have hc : ContinuousAt gagliardoSymbolKernel Real.pi := by
    unfold gagliardoSymbolKernel
    exact (continuous_const.sub (continuous_const.mul Real.continuous_cos)).continuousAt.div
      (continuous_id.pow 2).continuousAt (pow_ne_zero 2 Real.pi_ne_zero)
  have hπ : gagliardoSymbolKernel Real.pi ≠ 0 := by
    simp [gagliardoSymbolKernel, Real.cos_pi, Real.pi_ne_zero]
  apply (integral_pos_iff_support_of_nonneg gagliardoSymbolKernel_nonneg gagliardoSymbolKernel_integrable).2
  exact Measure.measure_pos_of_mem_nhds volume (hc.eventually_ne hπ)

/-- The frequency-scaled difference quotient is a rescaling of the fixed
integrable kernel, including the totalized zero value at h=0. -/
theorem gagliardoSymbolKernel_scaled {ξ : ℝ} (hξ : ξ ≠ 0) (h : ℝ) :
    (2 - 2 * Real.cos (h * ξ)) / h ^ 2 = ξ ^ 2 * gagliardoSymbolKernel (h * ξ) := by
  by_cases hh : h = 0
  · simp [hh, gagliardoSymbolKernel]
  · unfold gagliardoSymbolKernel
    field_simp
    ring

theorem gagliardoSymbol_integrable (ξ : ℝ) :
    Integrable (fun h : ℝ => (2 - 2 * Real.cos (h * ξ)) / h ^ 2) := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  · have hi := (gagliardoSymbolKernel_integrable.comp_mul_right' hξ).const_mul (ξ ^ 2)
    exact hi.congr (ae_of_all _ fun h => (gagliardoSymbolKernel_scaled hξ h).symm)

/-- The actual Gagliardo multiplier is exactly homogeneous of order one. -/
theorem integral_gagliardoSymbol (ξ : ℝ) :
    (∫ h : ℝ, (2 - 2 * Real.cos (h * ξ)) / h ^ 2) = |ξ| * gagliardoSymbolConstant := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  · have heq : (fun h : ℝ => (2 - 2 * Real.cos (h * ξ)) / h ^ 2) =
        fun h : ℝ => ξ ^ 2 * gagliardoSymbolKernel (h * ξ) :=
      funext (gagliardoSymbolKernel_scaled hξ)
    rw [heq, integral_const_mul, Measure.integral_comp_mul_right]
    simp only [smul_eq_mul, abs_inv]
    change ξ ^ 2 * (|ξ|⁻¹ * gagliardoSymbolConstant) = |ξ| * gagliardoSymbolConstant
    rw [← sq_abs ξ]
    field_simp
    rw [← sq_abs ξ]
    ring

/-- The nonnegative-integral form is ready for Tonelli in the concrete
Gagliardo/Fourier identity. -/
theorem lintegral_gagliardoSymbol (ξ : ℝ) :
    (∫⁻ h : ℝ, ENNReal.ofReal ((2 - 2 * Real.cos (h * ξ)) / h ^ 2)) =
      ENNReal.ofReal |ξ| * ENNReal.ofReal gagliardoSymbolConstant := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gagliardoSymbol_integrable ξ)
    (ae_of_all _ fun h => div_nonneg
      (by linarith [Real.cos_le_one (h * ξ)]) (sq_nonneg h)),
    integral_gagliardoSymbol, ENNReal.ofReal_mul (abs_nonneg ξ)]

end Torsion.Spectral

module

public import Torsion.RestrictedSpectralGagliardo
public import Torsion.FourierParsevalApproximation
public import Torsion.RestrictedSpectralTranslation

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The actual Gagliardo representation on the closed restricted form domain

Translated compact smooth approximants converge in both original L¹ and L².
The proved Parseval extension therefore identifies every actual translated
difference. Nonnegative Tonelli and the exact cosine-symbol scaling extend
the core Gagliardo formula to every original restricted form member.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform

namespace Torsion.Spectral

/-- Translation commutes with convergence of differences in every Lᵖ norm
with p≥1. This is stated for the actual functions and original seminorms. -/
theorem tendsto_eLpNorm_translate_sub_error {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℝ → ℝ} {v : ℕ → ℝ → ℝ}
    (hf : MemLp f p volume) (hv : ∀ n, MemLp (v n) p volume)
    (hval : Tendsto (fun n => eLpNorm (fun x => v n x - f x) p volume) atTop (𝓝 0)) (h : ℝ) :
    Tendsto (fun n => eLpNorm (fun x =>
      (v n (x + h) - v n x) - (f (x + h) - f x)) p volume) atTop (𝓝 0) := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) h
  have hLt : MemLp (fun x => f (x + h)) p volume := hf.comp_measurePreserving hmp
  have hvLt (n : ℕ) : MemLp (fun x => v n (x + h)) p volume := (hv n).comp_measurePreserving hmp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hval.add hval) (fun _ => bot_le)
  intro n
  dsimp only
  have heq : (fun x => (v n (x + h) - v n x) - (f (x + h) - f x)) =
      fun x => (v n (x + h) - f (x + h)) + -(v n x - f x) := by funext x; ring
  rw [heq]
  calc
    _ ≤ eLpNorm (fun x => v n (x + h) - f (x + h)) p volume +
        eLpNorm (fun x => -(v n x - f x)) p volume :=
      eLpNorm_add_le hp
    _ = _ := by
      rw [show eLpNorm (fun x => v n (x + h) - f (x + h)) p volume =
          eLpNorm (fun x => v n x - f x) p volume from
            eLpNorm_comp_add_right (fun x => v n x - f x) h p]
      rw [show eLpNorm (fun x => -(v n x - f x)) p volume =
          eLpNorm (fun x => v n x - f x) p volume from by
            simpa only [Pi.neg_apply] using! eLpNorm_neg (fun x => v n x - f x) p volume]

/-- Exact translated Parseval for a genuine restricted form member. Its
translated density need not have restricted support: both actual L¹ and L²
approximations justify the generic Fourier Parseval extension. -/
theorem MemRestrictedFormDomain.integral_sq_translate_sub {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (h : ℝ) :
    (∫ x : ℝ, (f (x + h) - f x) ^ 2) =
      (1 / (2 * Real.pi)) *
        ∫ ξ : ℝ, (2 - 2 * Real.cos (h * ξ)) * ‖fourier f ξ‖ ^ 2 := by
  obtain ⟨v, hv, hval, _⟩ := hf.2.2.2
  have hvL (n : ℕ) : MemLp (v n) 2 volume := (hv n).memRestrictedFormDomain.1
  have hvI (n : ℕ) : Integrable (v n) := (hv n).memRestrictedFormDomain.integrable
  have hval1 := tendsto_eLpNorm_one_of_two_zero_exterior hvL hf.1
    (fun n => (hv n).memRestrictedFormDomain.2.2.1) hf.2.2.1 hval
  have hdiffL := (hf.1.comp_measurePreserving (measurePreserving_add_right volume h)).sub hf.1
  have hdiffI := (hf.integrable.comp_add_right h).sub hf.integrable
  have hdiffcore (n : ℕ) : ContDiff ℝ ∞ (fun x => v n (x + h) - v n x) ∧
      HasCompactSupport (fun x => v n (x + h) - v n x) := by
    refine ⟨((hv n).1.comp (contDiff_id.add contDiff_const)).sub (hv n).1, ?_⟩
    exact ((hv n).2.1.comp_homeomorph (Homeomorph.addRight h)).sub (hv n).2.1
  have hparseval := (fourier_parseval_of_compactSmooth_approximation hdiffL hdiffI hdiffcore
    (tendsto_eLpNorm_translate_sub_error (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf.1 hvL hval h)
    (tendsto_eLpNorm_translate_sub_error (by norm_num : (1 : ℝ≥0∞) ≤ 1)
      (memLp_one_iff_integrable.2 hf.integrable)
      (fun n => memLp_one_iff_integrable.2 (hvI n)) hval1 h)).2
  have hfreq : (∫ ξ : ℝ, ‖fourier (fun x => f (x + h) - f x) ξ‖ ^ 2) =
      ∫ ξ : ℝ, (2 - 2 * Real.cos (h * ξ)) * ‖fourier f ξ‖ ^ 2 := by
    apply integral_congr_ae
    exact ae_of_all _ fun ξ => by
      dsimp only
      rw [fourier_translate_sub hf.integrable, norm_mul, mul_pow, norm_exp_phase_sub_one_sq]
  change (∫ ξ : ℝ, ‖fourier (fun x => f (x + h) - f x) ξ‖ ^ 2) =
    (2 * Real.pi) * ∫ x : ℝ, (f (x + h) - f x) ^ 2 at hparseval
  rw [hfreq] at hparseval
  rw [hparseval]
  field_simp [Real.pi_ne_zero]

/-- Every translated squared quotient of an original form member is
integrable in the physical variable. -/
theorem MemRestrictedFormDomain.integrable_sq_translate_quotient {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (h : ℝ) :
    Integrable (fun x : ℝ => (f (x + h) - f x) ^ 2 / h ^ 2) := by
  have hdiff := (hf.1.comp_measurePreserving (measurePreserving_add_right volume h)).sub hf.1
  have hs := (memLp_two_iff_integrable_sq_norm hdiff.aestronglyMeasurable).1 hdiff
  have hi : Integrable (fun x : ℝ => (f (x + h) - f x) ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply, Function.comp_apply] using! hs
  exact hi.div_const _

/-- The bounded cosine multiplier is integrable against the genuine
unweighted Fourier L² mass of every original form member. -/
theorem MemRestrictedFormDomain.integrable_fourier_translate_quotient {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (h : ℝ) :
    Integrable (fun ξ : ℝ => ((2 - 2 * Real.cos (h * ξ)) / h ^ 2) * ‖fourier f ξ‖ ^ 2) := by
  have hF := fourier_continuous hf.integrable
  have hi := (memLp_two_iff_integrable_sq_norm hf.fourier_parseval.1.aestronglyMeasurable).1 hf.fourier_parseval.1
  have hm : AEStronglyMeasurable
      (fun ξ : ℝ => ((2 - 2 * Real.cos (h * ξ)) / h ^ 2) * ‖fourier f ξ‖ ^ 2) volume := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  apply (hi.const_mul (4 / h ^ 2)).mono' hm
  exact ae_of_all _ fun ξ => by
    have hn : 0 ≤ 2 - 2 * Real.cos (h * ξ) := by nlinarith [Real.cos_le_one (h * ξ)]
    have hb : 2 - 2 * Real.cos (h * ξ) ≤ 4 := by nlinarith [Real.neg_one_le_cos (h * ξ)]
    rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg hn (sq_nonneg h)) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb (sq_nonneg h)) (sq_nonneg _)

/-- Exact translated quotient Parseval for original form members. -/
theorem MemRestrictedFormDomain.integral_sq_translate_quotient {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (h : ℝ) :
    (∫ x : ℝ, (f (x + h) - f x) ^ 2 / h ^ 2) =
      (1 / (2 * Real.pi)) *
        ∫ ξ : ℝ, ((2 - 2 * Real.cos (h * ξ)) / h ^ 2) * ‖fourier f ξ‖ ^ 2 := by
  rw [integral_div, hf.integral_sq_translate_sub]
  calc
    _ = (1 / (2 * Real.pi)) *
        ((∫ ξ : ℝ, (2 - 2 * Real.cos (h * ξ)) * ‖fourier f ξ‖ ^ 2) / h ^ 2) := by ring
    _ = _ := by
      rw [← integral_div]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun ξ => by dsimp only; ring

/-- Genuine exact Gagliardo representation of the existing Fourier form
on its original closed restricted domain, not only on smooth functions. -/
theorem MemRestrictedFormDomain.gagliardoEnergy {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) :
    gagliardoEnergy f = ENNReal.ofReal (gagliardoSymbolConstant * energy f f) := by
  have hinner (h : ℝ) :
      (∫⁻ x : ℝ, ENNReal.ofReal ((f (x + h) - f x) ^ 2 / h ^ 2)) =
        ENNReal.ofReal (1 / (2 * Real.pi)) *
          ∫⁻ ξ : ℝ, ENNReal.ofReal ((2 - 2 * Real.cos (h * ξ)) / h ^ 2) *
            ENNReal.ofReal (‖fourier f ξ‖ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrable_sq_translate_quotient h)
      (ae_of_all _ fun x => div_nonneg (sq_nonneg _) (sq_nonneg _)),
      hf.integral_sq_translate_quotient,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi)),
      ofReal_integral_eq_lintegral_ofReal (hf.integrable_fourier_translate_quotient h)
        (ae_of_all _ fun ξ => mul_nonneg
          (div_nonneg (by nlinarith [Real.cos_le_one (h * ξ)]) (sq_nonneg _)) (sq_nonneg _))]
    congr 1
    apply lintegral_congr
    intro ξ
    rw [ENNReal.ofReal_mul (div_nonneg (by nlinarith [Real.cos_le_one (h * ξ)]) (sq_nonneg _))]
  unfold Torsion.Spectral.gagliardoEnergy
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hF := fourier_continuous hf.integrable
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((2 - 2 * Real.cos (p.1 * p.2)) / p.1 ^ 2) *
        ENNReal.ofReal (‖fourier f p.2‖ ^ 2)) := by
    fun_prop
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hsymbol (ξ : ℝ) :
      (∫⁻ h : ℝ, ENNReal.ofReal ((2 - 2 * Real.cos (h * ξ)) / h ^ 2) * ENNReal.ofReal (‖fourier f ξ‖ ^ 2)) =
        ENNReal.ofReal (|ξ| * ‖fourier f ξ‖ ^ 2) * ENNReal.ofReal gagliardoSymbolConstant := by
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_gagliardoSymbol,
      ENNReal.ofReal_mul (abs_nonneg ξ)]
    ring
  simp_rw [hsymbol]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hf.2.1
      (ae_of_all _ fun ξ => mul_nonneg (abs_nonneg ξ) (sq_nonneg _)),
    energy_self, ENNReal.ofReal_mul gagliardoSymbolConstant_pos.le,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  ring

end Torsion.Spectral

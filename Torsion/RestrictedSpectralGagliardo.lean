module

public import Torsion.FourierPlancherel
public import Torsion.RestrictedSpectralEnergyContinuity
public import Torsion.RestrictedSpectralGagliardoSymbol
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Translation and Gagliardo foundations for the actual Fourier form

These results concern the existing exp(-ixξ) Fourier transform. Translated
compact smooth functions satisfy its exact Parseval identity, which is the
frequency-space starting point for a real-space Markov contraction.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform

namespace Torsion.Spectral

/-- Translation of the source-normalized actual Fourier transform. -/
theorem fourier_translate (f : ℝ → ℝ) (h ξ : ℝ) :
    fourier (fun x => f (x + h)) ξ =
      Complex.exp ((h * ξ : ℝ) * Complex.I) * fourier f ξ := by
  have hshift := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => Complex.exp (-(((x - h) * ξ : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) h
  have heq : fourier (fun x => f (x + h)) ξ =
      ∫ x : ℝ, Complex.exp (-(((x - h) * ξ : ℝ) : ℂ) * Complex.I) * (f x : ℂ) := by
    simpa only [fourier, add_sub_cancel_right] using hshift
  rw [heq]
  unfold fourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    have hphase : Complex.exp (-(((x - h) * ξ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((h * ξ : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hphase]
    ring

/-- The squared phase increment is the nonnegative real cosine symbol. -/
theorem norm_exp_phase_sub_one_sq (u : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos u := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.one_re, Complex.one_im, sub_zero]
  nlinarith [Real.sin_sq_add_cos_sq u]

/-- The Fourier transform of an actual translated difference, with no
smoothness or spectral assumption on the density. -/
theorem fourier_translate_sub {f : ℝ → ℝ} (hf : Integrable f) (h ξ : ℝ) :
    fourier (fun x => f (x + h) - f x) ξ =
      (Complex.exp (((h * ξ : ℝ) : ℂ) * Complex.I) - 1) * fourier f ξ := by
  rw [fourier_sub (hf.comp_add_right h) hf]
  simp only [Pi.sub_apply]
  rw [fourier_translate]
  ring

/-- The exact translated-difference Parseval identity for the original
compact smooth Fourier core. -/
theorem integral_sq_translate_sub_of_core {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h : ℝ) :
    (∫ x : ℝ, (f (x + h) - f x) ^ 2) =
      (1 / (2 * Real.pi)) *
        ∫ ξ : ℝ, (2 - 2 * Real.cos (h * ξ)) * ‖fourier f ξ‖ ^ 2 := by
  have htrans : ContDiff ℝ ∞ (fun x : ℝ => f (x + h)) :=
    hf.comp (contDiff_id.add contDiff_const)
  have htransc : HasCompactSupport (fun x : ℝ => f (x + h)) :=
    hc.comp_homeomorph (Homeomorph.addRight h)
  have hdiffc : HasCompactSupport (fun x : ℝ => f (x + h) - f x) :=
    htransc.comp₂_left hc (sub_self (0 : ℝ))
  have hparseval := integral_norm_sq_fourier_of_core (htrans.sub hf) hdiffc
  have hfreq : (∫ ξ : ℝ, ‖fourier (fun x => f (x + h) - f x) ξ‖ ^ 2) =
      ∫ ξ : ℝ, (2 - 2 * Real.cos (h * ξ)) * ‖fourier f ξ‖ ^ 2 := by
    apply integral_congr_ae
    exact ae_of_all _ fun ξ => by
      dsimp only
      rw [fourier_translate_sub (hf.continuous.integrable_of_hasCompactSupport hc),
        norm_mul, mul_pow, norm_exp_phase_sub_one_sq]
  rw [hfreq] at hparseval
  rw [hparseval]
  field_simp [Real.pi_ne_zero]

/-- The actual real-space Gagliardo seminorm, with its full nonnegative
extended integral. Its identification with the original Fourier energy
is a separate theorem; this definition does not change that energy. -/
def gagliardoEnergy (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ h : ℝ, ∫⁻ x : ℝ, ENNReal.ofReal ((f (x + h) - f x) ^ 2 / h ^ 2)

/-- Every real 1-Lipschitz scalar contraction decreases the actual
real-space difference integral, directly from its pointwise estimate. -/
theorem gagliardoEnergy_comp_le {f Φ : ℝ → ℝ}
    (hΦ : ∀ x y : ℝ, |Φ x - Φ y| ≤ |x - y|) :
    gagliardoEnergy (fun x => Φ (f x)) ≤ gagliardoEnergy f := by
  apply lintegral_mono
  intro h
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (sq_nonneg h)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hΦ (f (x + h)) (f x)) 2

/-- Absolute value contracts the actual real-space Gagliardo integral. -/
theorem gagliardoEnergy_abs_le (f : ℝ → ℝ) :
    gagliardoEnergy (fun x => |f x|) ≤ gagliardoEnergy f :=
  gagliardoEnergy_comp_le (fun x y => abs_abs_sub_abs_le_abs_sub x y)


/-- The physical squared translated quotient is genuinely integrable for
all translations of a compact smooth function, including h=0. -/
set_option maxHeartbeats 800000 in
theorem integrable_sq_translate_quotient_of_core {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h : ℝ) :
    Integrable (fun x : ℝ => (f (x + h) - f x) ^ 2 / h ^ 2) := by
  have htrans : ContDiff ℝ ∞ (fun x : ℝ => f (x + h)) :=
    hf.comp (contDiff_id.add contDiff_const)
  have htransc : HasCompactSupport (fun x : ℝ => f (x + h)) :=
    hc.comp_homeomorph (Homeomorph.addRight h)
  have hdiffc : HasCompactSupport (fun x : ℝ => f (x + h) - f x) :=
    htransc.comp₂_left hc (sub_self (0 : ℝ))
  exact (((htrans.sub hf).continuous.pow 2).integrable_of_hasCompactSupport
    (hdiffc.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num))).div_const _

/-- The nonnegative frequency translated quotient is integrable, from the
bounded cosine increment and the already proved source Parseval theorem. -/
theorem integrable_fourier_translate_quotient_of_core {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h : ℝ) :
    Integrable (fun ξ : ℝ => ((2 - 2 * Real.cos (h * ξ)) / h ^ 2) * ‖fourier f ξ‖ ^ 2) := by
  have hF := fourier_continuous (hf.continuous.integrable_of_hasCompactSupport hc)
  have hm : AEStronglyMeasurable
      (fun ξ : ℝ => ((2 - 2 * Real.cos (h * ξ)) / h ^ 2) * ‖fourier f ξ‖ ^ 2) volume := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  apply ((integrable_norm_sq_fourier_of_core hf hc).const_mul (4 / h ^ 2)).mono' hm
  exact ae_of_all _ fun ξ => by
    have hn : 0 ≤ 2 - 2 * Real.cos (h * ξ) := by nlinarith [Real.cos_le_one (h * ξ)]
    have hb : 2 - 2 * Real.cos (h * ξ) ≤ 4 := by nlinarith [Real.neg_one_le_cos (h * ξ)]
    rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg hn (sq_nonneg h)) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb (sq_nonneg h)) (sq_nonneg _)

/-- Exact source-normalized Parseval for the squared difference quotient. -/
theorem integral_sq_translate_quotient_of_core {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (h : ℝ) :
    (∫ x : ℝ, (f (x + h) - f x) ^ 2 / h ^ 2) =
      (1 / (2 * Real.pi)) *
        ∫ ξ : ℝ, ((2 - 2 * Real.cos (h * ξ)) / h ^ 2) * ‖fourier f ξ‖ ^ 2 := by
  rw [integral_div, integral_sq_translate_sub_of_core hf hc]
  calc
    _ = (1 / (2 * Real.pi)) *
        ((∫ ξ : ℝ, (2 - 2 * Real.cos (h * ξ)) * ‖fourier f ξ‖ ^ 2) / h ^ 2) := by ring
    _ = _ := by
      rw [← integral_div]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun ξ => by dsimp only; ring

/-- The real-space seminorm has an exact iterated frequency representation
on the actual compact smooth core, justified by nonnegative Tonelli. -/
theorem gagliardoEnergy_eq_frequency_iterated_of_core {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    gagliardoEnergy f = ENNReal.ofReal (1 / (2 * Real.pi)) *
      ∫⁻ ξ : ℝ, ENNReal.ofReal (‖fourier f ξ‖ ^ 2) *
        ∫⁻ h : ℝ, ENNReal.ofReal ((2 - 2 * Real.cos (h * ξ)) / h ^ 2) := by
  have hinner (h : ℝ) :
      (∫⁻ x : ℝ, ENNReal.ofReal ((f (x + h) - f x) ^ 2 / h ^ 2)) =
        ENNReal.ofReal (1 / (2 * Real.pi)) *
          ∫⁻ ξ : ℝ, ENNReal.ofReal ((2 - 2 * Real.cos (h * ξ)) / h ^ 2) *
            ENNReal.ofReal (‖fourier f ξ‖ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sq_translate_quotient_of_core hf hc h)
      (ae_of_all _ fun x => div_nonneg (sq_nonneg _) (sq_nonneg _)),
      integral_sq_translate_quotient_of_core hf hc,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi)),
      ofReal_integral_eq_lintegral_ofReal (integrable_fourier_translate_quotient_of_core hf hc h)
        (ae_of_all _ fun ξ => mul_nonneg
          (div_nonneg (by nlinarith [Real.cos_le_one (h * ξ)]) (sq_nonneg _)) (sq_nonneg _))]
    congr 1
    apply lintegral_congr
    intro ξ
    rw [ENNReal.ofReal_mul (div_nonneg (by nlinarith [Real.cos_le_one (h * ξ)]) (sq_nonneg _))]
  unfold gagliardoEnergy
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  have hF := fourier_continuous (hf.continuous.integrable_of_hasCompactSupport hc)
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((2 - 2 * Real.cos (p.1 * p.2)) / p.1 ^ 2) *
        ENNReal.ofReal (‖fourier f p.2‖ ^ 2)) := by
    fun_prop
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro ξ
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]


/-- Genuine real-space representation of the existing Fourier energy on
the compact smooth core. The exact positive universal constant is retained
as its actual convergent cosine integral; its numerical evaluation is not
needed for Markov contraction. -/
theorem gagliardoEnergy_of_core {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    gagliardoEnergy f = ENNReal.ofReal (gagliardoSymbolConstant * energy f f) := by
  rw [gagliardoEnergy_eq_frequency_iterated_of_core hf hc]
  simp_rw [lintegral_gagliardoSymbol]
  have hbody (ξ : ℝ) : ENNReal.ofReal (‖fourier f ξ‖ ^ 2) *
        (ENNReal.ofReal |ξ| * ENNReal.ofReal gagliardoSymbolConstant) =
      ENNReal.ofReal (|ξ| * ‖fourier f ξ‖ ^ 2) * ENNReal.ofReal gagliardoSymbolConstant := by
    rw [ENNReal.ofReal_mul (abs_nonneg ξ)]
    ring
  simp_rw [hbody]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal
      (finiteEnergy_of_contDiff_hasCompactSupport hf hc)
      (ae_of_all _ fun ξ => mul_nonneg (abs_nonneg ξ) (sq_nonneg _)),
    energy_self, ENNReal.ofReal_mul gagliardoSymbolConstant_pos.le,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  ring

/-- Every smooth scalar 1-Lipschitz contraction fixing zero decreases the
original concrete Fourier energy on its actual compact smooth core. -/
theorem energy_comp_le_of_core {f Φ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦ0 : Φ 0 = 0)
    (hLip : ∀ x y : ℝ, |Φ x - Φ y| ≤ |x - y|) :
    energy (fun x => Φ (f x)) (fun x => Φ (f x)) ≤ energy f f := by
  have hcomp : ContDiff ℝ ∞ (fun x => Φ (f x)) := hΦ.comp hf
  have hcompc : HasCompactSupport (fun x => Φ (f x)) := hc.comp_left hΦ0
  have hG := gagliardoEnergy_comp_le (f := f) hLip
  rw [gagliardoEnergy_of_core hcomp hcompc, gagliardoEnergy_of_core hf hc] at hG
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg gagliardoSymbolConstant_pos.le (energy_nonneg f))).1 hG
  exact (mul_le_mul_iff_left₀ gagliardoSymbolConstant_pos).1 hreal

end Torsion.Spectral

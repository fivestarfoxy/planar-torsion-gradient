module

public import Torsion.RestrictedSpectralComposition
public import Torsion.RestrictedSpectralFourierBounds

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Global weak Fourier identification

Schwartz test separation identifies an actual integrable whole-line
half-Laplacian density with the concrete multiplier `|ξ|`. This module
keeps the original source Fourier transform and original real energy.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- A continuous real-linear map sends a Schwartz function to an actual
Schwartz function. -/
def schwartzPostcomp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (S : 𝓢(ℝ, E)) : 𝓢(ℝ, F) where
  toFun x := L (S x)
  smooth' := L.contDiff.comp S.smooth'
  decay' k n := by
    refine ⟨‖L‖ * SchwartzMap.seminorm ℝ k n S, fun x => ?_⟩
    have hi := L.iteratedFDeriv_comp_left (x := x) S.smooth'.contDiffAt
      (show (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (L ∘ S.toFun) x‖ ≤ _
    rw [hi]
    calc
      ‖x‖ ^ k * ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ n S x)‖ ≤
          ‖x‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ n S x‖) := by
        gcongr
        exact L.norm_compContinuousMultilinearMap_le _
      _ ≤ _ := by
        rw [mul_left_comm]
        exact mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℝ k n S x) (norm_nonneg _)

/-- Complex source Fourier transform used only for complex test algebra;
the original real-valued transform is unchanged. -/
def complexSourceFourier (S : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  𝓕 S (ξ / (2 * Real.pi))

theorem complexSourceFourier_eq_integral (S : ℝ → ℂ) (ξ : ℝ) :
    complexSourceFourier S ξ =
      ∫ x : ℝ, Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) * S x := by
  rw [complexSourceFourier, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have h : -2 * Real.pi * x * (ξ / (2 * Real.pi)) = -(x * ξ) := by field_simp; ring
    simp only [h, Complex.ofReal_neg, smul_eq_mul]

theorem complexSourceFourier_ofReal (f : ℝ → ℝ) :
    complexSourceFourier (fun x => (f x : ℂ)) = fourier f := by
  ext ξ
  exact (fourier_eq_mathlib f ξ).symm

theorem integrable_pow_mul_norm_complexSourceFourier (S : 𝓢(ℝ, ℂ)) (n : ℕ) :
    Integrable (fun ξ : ℝ => ‖ξ‖ ^ n * ‖complexSourceFourier S ξ‖) := by
  let FS := SchwartzMap.fourierTransformCLM ℂ S
  have hp : 0 < 2 * Real.pi := by positivity
  have hi := (FS.integrable_pow_mul volume n).comp_div hp.ne'
  convert hi.const_mul ((2 * Real.pi) ^ n) using 1
  funext ξ
  change ‖ξ‖ ^ n * ‖FS (ξ / (2 * Real.pi))‖ = _
  rw [norm_div, Real.norm_of_nonneg hp.le, div_pow]
  field_simp

theorem integrable_pow_mul_norm_fourier_of_schwartz (S : 𝓢(ℝ, ℝ)) (n : ℕ) :
    Integrable (fun ξ : ℝ => ‖ξ‖ ^ n * ‖fourier S ξ‖) := by
  have h := integrable_pow_mul_norm_complexSourceFourier
    (schwartzPostcomp Complex.ofRealCLM S) n
  change Integrable (fun ξ : ℝ => ‖ξ‖ ^ n *
    ‖complexSourceFourier (fun x : ℝ => (S x : ℂ)) ξ‖) at h
  rw [complexSourceFourier_ofReal] at h
  exact h

theorem fourier_neg_eq_star (f : ℝ → ℝ) (ξ : ℝ) :
    fourier f (-ξ) = star (fourier f ξ) := by
  rw [star_fourier_eq_integral_phase]
  unfold fourier
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp only [mul_neg, Complex.ofReal_neg, neg_neg]

theorem integrable_weighted_fourier_schwartz_pairing {f : ℝ → ℝ}
    (hf : Integrable f) (S : 𝓢(ℝ, ℝ)) (n : ℕ) :
    Integrable (fun ξ : ℝ => ((‖ξ‖ ^ n : ℝ) : ℂ) *
      (fourier f ξ * star (fourier S ξ))) := by
  apply ((integrable_pow_mul_norm_fourier_of_schwartz S n).const_mul
    (∫ x : ℝ, ‖f x‖)).mono'
  · exact (Complex.continuous_ofReal.comp (continuous_norm.pow n)).aestronglyMeasurable.mul
      ((fourier_continuous hf).aestronglyMeasurable.mul
        (fourier_continuous S.integrable).star.aestronglyMeasurable)
  · exact ae_of_all _ fun ξ => by
      simp only [norm_mul, Complex.norm_real, norm_pow, norm_norm, norm_star]
      calc
        ‖ξ‖ ^ n * (‖fourier f ξ‖ * ‖fourier S ξ‖) ≤
            ‖ξ‖ ^ n * ((∫ x : ℝ, ‖f x‖) * ‖fourier S ξ‖) := by
          gcongr
          exact norm_fourier_le_integral_norm f ξ
        _ = _ := by ring

/-- The full complex weighted pairing of two real densities is real.
Reflection proves this directly for the original Fourier integrals. -/
theorem integral_weighted_fourier_pairing_eq_ofReal {f g : ℝ → ℝ} (n : ℕ)
    (hi : Integrable (fun ξ : ℝ => ((‖ξ‖ ^ n : ℝ) : ℂ) *
      (fourier f ξ * star (fourier g ξ)))) :
    (∫ ξ : ℝ, ((‖ξ‖ ^ n : ℝ) : ℂ) * (fourier f ξ * star (fourier g ξ))) =
      ((∫ ξ : ℝ, ‖ξ‖ ^ n * (fourier f ξ * star (fourier g ξ)).re : ℝ) : ℂ) := by
  let J : ℂ := ∫ ξ : ℝ, ((‖ξ‖ ^ n : ℝ) : ℂ) *
    (fourier f ξ * star (fourier g ξ))
  have hstar : star J = J := by
    dsimp only [J]
    rw [Complex.star_def, ← integral_conj]
    calc
      _ = ∫ ξ : ℝ, ((‖-ξ‖ ^ n : ℝ) : ℂ) *
          (fourier f (-ξ) * star (fourier g (-ξ))) := by
        apply integral_congr_ae
        exact ae_of_all _ fun ξ => by
          dsimp only
          simp only [fourier_neg_eq_star, norm_neg, map_mul, Complex.star_def,
            Complex.conj_ofReal, Complex.conj_conj]
      _ = _ := by
        simpa only [Complex.star_def] using integral_neg_eq_self
          (fun ξ : ℝ => ((‖ξ‖ ^ n : ℝ) : ℂ) *
            (fourier f ξ * star (fourier g ξ))) volume
  have hJim : J.im = 0 := by
    have h := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  apply Complex.ext
  · have hRe : J.re = ∫ ξ : ℝ,
        (((‖ξ‖ ^ n : ℝ) : ℂ) * (fourier f ξ * star (fourier g ξ))).re :=
      (integral_re hi).symm
    simpa only [J, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hRe
  · simpa only [J, Complex.ofReal_im] using hJim

theorem integral_weighted_fourier_schwartz_pairing {f : ℝ → ℝ}
    (hf : Integrable f) (S : 𝓢(ℝ, ℝ)) :
    (∫ ξ : ℝ, ((|ξ| : ℝ) : ℂ) * (fourier f ξ * star (fourier S ξ))) =
      ((2 * Real.pi * energy f S : ℝ) : ℂ) := by
  have h := integral_weighted_fourier_pairing_eq_ofReal 1
    (integrable_weighted_fourier_schwartz_pairing hf S 1)
  simp only [pow_one, Real.norm_eq_abs] at h
  rw [h]
  congr 1
  unfold energy
  field_simp

theorem integral_fourier_schwartz_pairing {f : ℝ → ℝ}
    (hf : Integrable f) (S : 𝓢(ℝ, ℝ)) :
    (∫ ξ : ℝ, fourier f ξ * star (fourier S ξ)) =
      ((2 * Real.pi * ∫ x : ℝ, f x * S x : ℝ) : ℂ) := by
  let SC := schwartzPostcomp Complex.ofRealCLM S
  have hpair := integral_mathlib_fourier_mul_star_schwartz hf SC
  have hp : 0 < 2 * Real.pi := by positivity
  calc
    _ = ∫ ξ : ℝ, 𝓕 (fun x => (f x : ℂ)) (ξ / (2 * Real.pi)) *
        star (𝓕 SC (ξ / (2 * Real.pi))) := by
      simp only [fourier_eq_mathlib]
      rfl
    _ = ((2 * Real.pi : ℝ) : ℂ) * ∫ ξ : ℝ,
        𝓕 (fun x => (f x : ℂ)) ξ * star (𝓕 SC ξ) := by
      simpa only [smul_eq_mul, abs_of_pos hp] using
        Measure.integral_comp_div (fun ξ : ℝ =>
          𝓕 (fun x => (f x : ℂ)) ξ * star (𝓕 SC ξ)) (2 * Real.pi)
    _ = _ := by
      rw [hpair]
      have heq : (fun x : ℝ => (f x : ℂ) * star (SC x)) =
          fun x => ((f x * S x : ℝ) : ℂ) := by
        funext x
        change (f x : ℂ) * star (S x : ℂ) = _
        simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
      rw [heq, integral_complex_ofReal, ← Complex.ofReal_mul]

theorem complexSourceFourier_eq_re_add_im (S : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    complexSourceFourier S ξ = fourier (fun x => (S x).re) ξ +
      Complex.I * fourier (fun x => (S x).im) ξ := by
  rw [complexSourceFourier_eq_integral]
  have hre : Integrable (fun x : ℝ => (S x).re) := S.integrable.re
  have him : Integrable (fun x : ℝ => (S x).im) := S.integrable.im
  unfold fourier
  rw [← integral_const_mul, ← integral_add (integrable_fourier_phase_mul hre ξ)
    ((integrable_fourier_phase_mul him ξ).const_mul Complex.I)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    have hS : S x = ((S x).re : ℂ) + Complex.I * ((S x).im : ℂ) := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hS]
    ring

theorem integral_fourier_complexSchwartz_pairing {f : ℝ → ℝ}
    (hf : Integrable f) (S : 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, fourier f ξ * star (complexSourceFourier S ξ)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ x : ℝ, (f x : ℂ) * star (S x) := by
  have hp : 0 < 2 * Real.pi := by positivity
  calc
    _ = ∫ ξ : ℝ, 𝓕 (fun x => (f x : ℂ)) (ξ / (2 * Real.pi)) *
        star (𝓕 S (ξ / (2 * Real.pi))) := by simp only [fourier_eq_mathlib, complexSourceFourier]
    _ = ((2 * Real.pi : ℝ) : ℂ) * ∫ ξ : ℝ,
        𝓕 (fun x => (f x : ℂ)) ξ * star (𝓕 S ξ) := by
      simpa only [smul_eq_mul, abs_of_pos hp] using
        Measure.integral_comp_div (fun ξ : ℝ =>
          𝓕 (fun x => (f x : ℂ)) ξ * star (𝓕 S ξ)) (2 * Real.pi)
    _ = _ := by rw [integral_mathlib_fourier_mul_star_schwartz hf S]

/-- Real Schwartz equations also give the full complex Schwartz equation,
by taking the actual real and imaginary parts of the test. -/
theorem complex_schwartz_equation_of_real {f q : ℝ → ℝ}
    (hf : Integrable f) (hq : Integrable q)
    (hweak : ∀ S : 𝓢(ℝ, ℝ), energy f S = ∫ x : ℝ, q x * S x)
    (S : 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, ((|ξ| : ℝ) : ℂ) * (fourier f ξ * star (complexSourceFourier S ξ))) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ x : ℝ, (q x : ℂ) * star (S x) := by
  let SR := schwartzPostcomp Complex.reCLM S
  let SI := schwartzPostcomp Complex.imCLM S
  have hIR := integrable_weighted_fourier_schwartz_pairing hf SR 1
  have hII := integrable_weighted_fourier_schwartz_pairing hf SI 1
  simp only [pow_one, Real.norm_eq_abs] at hIR hII
  have hr := integral_weighted_fourier_schwartz_pairing hf SR
  have hi := integral_weighted_fourier_schwartz_pairing hf SI
  rw [hweak SR] at hr
  rw [hweak SI] at hi
  have hqr : Integrable (fun x : ℝ => q x * SR x) := by
    have h := hq.bdd_mul' SR.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => SchwartzMap.norm_le_seminorm ℝ SR x)
    simpa only [mul_comm] using h
  have hqi : Integrable (fun x : ℝ => q x * SI x) := by
    have h := hq.bdd_mul' SI.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => SchwartzMap.norm_le_seminorm ℝ SI x)
    simpa only [mul_comm] using h
  have hspace : (∫ x : ℝ, (q x : ℂ) * star (S x)) =
      ((∫ x : ℝ, q x * SR x : ℝ) : ℂ) -
        Complex.I * ((∫ x : ℝ, q x * SI x : ℝ) : ℂ) := by
    have hqrc : Integrable (fun x : ℝ => ((q x * SR x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.integrable_comp hqr
    have hqic : Integrable (fun x : ℝ => ((q x * SI x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.integrable_comp hqi
    rw [← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_const_mul,
      ← integral_sub hqrc (hqic.const_mul Complex.I)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change (q x : ℂ) * star (S x) =
        ((q x * (S x).re : ℝ) : ℂ) - Complex.I * ((q x * (S x).im : ℝ) : ℂ)
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hfreq : (∫ ξ : ℝ, ((|ξ| : ℝ) : ℂ) *
        (fourier f ξ * star (complexSourceFourier S ξ))) =
      (∫ ξ : ℝ, ((|ξ| : ℝ) : ℂ) * (fourier f ξ * star (fourier SR ξ))) -
        Complex.I * ∫ ξ : ℝ, ((|ξ| : ℝ) : ℂ) * (fourier f ξ * star (fourier SI ξ)) := by
    rw [← integral_const_mul, ← integral_sub hIR (hII.const_mul Complex.I)]
    apply integral_congr_ae
    exact ae_of_all _ fun ξ => by
      dsimp only
      rw [complexSourceFourier_eq_re_add_im]
      change ((|ξ| : ℝ) : ℂ) * (fourier f ξ * star
          (fourier SR ξ + Complex.I * fourier SI ξ)) = _
      simp only [map_add, map_mul, Complex.star_def, Complex.conj_I]
      ring
  rw [hfreq, hr, hi, hspace]
  push_cast
  ring

theorem integrable_weighted_complexSchwartz_pairing {f : ℝ → ℝ}
    (hf : Integrable f) (S : 𝓢(ℝ, ℂ)) (n : ℕ) :
    Integrable (fun ξ : ℝ => ((‖ξ‖ ^ n : ℝ) : ℂ) *
      (fourier f ξ * star (complexSourceFourier S ξ))) := by
  apply ((integrable_pow_mul_norm_complexSourceFourier S n).const_mul
    (∫ x : ℝ, ‖f x‖)).mono'
  · have hFS : Continuous (complexSourceFourier S) :=
      (SchwartzMap.fourierTransformCLM ℂ S).continuous.comp (continuous_id.div_const _)
    exact (Complex.continuous_ofReal.comp (continuous_norm.pow n)).aestronglyMeasurable.mul
      ((fourier_continuous hf).aestronglyMeasurable.mul hFS.star.aestronglyMeasurable)
  · exact ae_of_all _ fun ξ => by
      simp only [norm_mul, Complex.norm_real, norm_pow, norm_norm, norm_star]
      calc
        ‖ξ‖ ^ n * (‖fourier f ξ‖ * ‖complexSourceFourier S ξ‖) ≤
            ‖ξ‖ ^ n * ((∫ x : ℝ, ‖f x‖) * ‖complexSourceFourier S ξ‖) := by
          gcongr
          exact norm_fourier_le_integral_norm f ξ
        _ = _ := by ring

end Torsion.Spectral

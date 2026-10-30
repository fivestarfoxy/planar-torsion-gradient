module

public import Torsion.FourierPlancherel
public import Torsion.FourierHilbertPairing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Squaring the actual Fourier multiplier against smooth tests

The source-normalized Fourier pairing with a compact smooth test follows
directly from Schwartz inversion and absolute Fubini. Consequently an
integrable density whose actual Fourier transform is `|ξ|` times that of
`f` has second half-Laplacian equal to the negative ordinary second
derivative of `f`, in the distributional test pairing. These are generic
operator identities; no concavity or boundary equation is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- Absolute Fourier pairing of an L¹ density and a Schwartz test, with
mathlib's normalization. -/
theorem integral_mathlib_fourier_mul_star_schwartz {f : ℝ → ℝ}
    (hf : Integrable f) (S : 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, 𝓕 (fun x => (f x : ℂ)) ξ * star (𝓕 S ξ)) =
      ∫ x : ℝ, (f x : ℂ) * star (S x) := by
  let FS : 𝓢(ℝ, ℂ) := SchwartzMap.fourierTransformCLM ℂ S
  have hfc := Complex.ofRealCLM.integrable_comp hf
  have hgc : Integrable (fun ξ : ℝ => star (𝓕 S ξ)) := by
    change Integrable (fun ξ : ℝ => star (FS ξ))
    simpa only [Complex.conjCLE_apply, Complex.star_def] using!
      (Complex.conjCLE.toContinuousLinearMap.integrable_comp (FS.integrable (μ := volume)))
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (L := innerₗ ℝ) (μ := volume) (ν := volume) (ContinuousLinearMap.mul ℂ ℂ)
    Real.continuous_fourierChar continuous_inner hfc hgc
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact real_inner_comm x y
  rw [hflip] at h
  change (∫ ξ : ℝ, 𝓕 (fun x => (f x : ℂ)) ξ * star (𝓕 S ξ)) =
    ∫ x : ℝ, (f x : ℂ) * 𝓕 (fun ξ => star (𝓕 S ξ)) x at h
  have hinv : 𝓕⁻ (fun ξ : ℝ => 𝓕 S ξ) = (S : ℝ → ℂ) := by
    simpa only [SchwartzMap.fourier_coe] using!
      (S.continuous.fourierInv_fourier_eq S.integrable (FS.integrable (μ := volume)))
  simpa only [mathlib_fourier_conj, hinv] using h

/-- Every polynomially weighted absolute Fourier moment of a compact
smooth test is integrable in the original normalization. -/
theorem integrable_pow_mul_norm_fourier_of_compactSmooth {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (n : ℕ) :
    Integrable (fun ξ : ℝ => ‖ξ‖ ^ n * ‖fourier ψ ξ‖) := by
  let S := SchwartzMap.fourierTransformCLM ℂ (compactSmoothSchwartz hψ hc)
  have hp : 0 < 2 * Real.pi := by positivity
  have hi := (S.integrable_pow_mul volume n).comp_div hp.ne'
  convert hi.const_mul ((2 * Real.pi) ^ n) using 1
  funext ξ
  rw [fourier_eq_mathlib]
  change ‖ξ‖ ^ n * ‖S (ξ / (2 * Real.pi))‖ = _
  rw [norm_div, Real.norm_of_nonneg hp.le, div_pow]
  field_simp

/-- Fourier L¹ pairing against the actual compact smooth core, without
an L² hypothesis on the first density. -/
theorem integral_fourier_pairing_of_compactSmooth {f ψ : ℝ → ℝ}
    (hf : Integrable f) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ ξ : ℝ, (fourier f ξ * star (fourier ψ ξ)).re) =
      (2 * Real.pi) * ∫ x : ℝ, f x * ψ x := by
  let S := compactSmoothSchwartz hψ hc
  have hpair := integral_mathlib_fourier_mul_star_schwartz hf S
  have hp : 0 < 2 * Real.pi := by positivity
  have hscaled : (∫ ξ : ℝ, fourier f ξ * star (fourier ψ ξ)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ x : ℝ, (f x : ℂ) * (ψ x : ℂ) := by
    calc
      _ = ∫ ξ : ℝ, 𝓕 (fun x => (f x : ℂ)) (ξ / (2 * Real.pi)) *
          star (𝓕 S (ξ / (2 * Real.pi))) := by
        simp only [fourier_eq_mathlib]
        rfl
      _ = ((2 * Real.pi : ℝ) : ℂ) * ∫ ξ : ℝ,
          𝓕 (fun x => (f x : ℂ)) ξ * star (𝓕 S ξ) := by
        simpa only [smul_eq_mul, Complex.real_smul, abs_of_pos hp] using!
          Measure.integral_comp_div (fun ξ : ℝ =>
            𝓕 (fun x => (f x : ℂ)) ξ * star (𝓕 S ξ)) (2 * Real.pi)
      _ = _ := by
        rw [hpair]
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change (f x : ℂ) * star (ψ x : ℂ) = _
          simp only [Complex.star_def, Complex.conj_ofReal]
  have hi : Integrable (fun ξ : ℝ => fourier f ξ * star (fourier ψ ξ)) := by
    apply ((integrable_pow_mul_norm_fourier_of_compactSmooth hψ hc 0).const_mul
      (∫ x : ℝ, ‖f x‖)).mono'
    · exact (fourier_continuous hf).aestronglyMeasurable.mul
        (fourier_continuous (hψ.continuous.integrable_of_hasCompactSupport hc)).star.aestronglyMeasurable
    · exact ae_of_all _ fun ξ => by
        simpa only [pow_zero, one_mul, norm_mul, norm_star, mul_comm] using
          mul_le_mul_of_nonneg_right (norm_fourier_le_integral_norm f ξ) (norm_nonneg (fourier ψ ξ))
  have hr := congrArg Complex.re hscaled
  have hRe : (∫ ξ : ℝ, fourier f ξ * star (fourier ψ ξ)).re =
      ∫ ξ : ℝ, (fourier f ξ * star (fourier ψ ξ)).re := (integral_re hi).symm
  rw [hRe] at hr
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_re] using hr

/-- The square of the genuine source-normalized half-Laplacian
multiplier is the negative second derivative, in actual smooth test
pairings. The Fourier multiplier hypothesis can be supplied by a global
weak identification; it is not a pointwise operator formula. -/
theorem energy_eq_neg_integral_second_deriv_of_fourier_mul_abs
    {f q ψ : ℝ → ℝ} (hf : Integrable f)
    (hF : ∀ ξ : ℝ, fourier q ξ = ((|ξ| : ℝ) : ℂ) * fourier f ξ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    energy q ψ = -(∫ x : ℝ, f x * deriv (deriv ψ) x) := by
  have hd : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv ψ)) := (contDiff_infty_iff_deriv.mp hd).2
  have hdi : Integrable (deriv ψ) := hd.continuous.integrable_of_hasCompactSupport hc.deriv
  have hddi : Integrable (deriv (deriv ψ)) :=
    hdd.continuous.integrable_of_hasCompactSupport hc.deriv.deriv
  have hFd (ξ : ℝ) : fourier (deriv (deriv ψ)) ξ =
      -((ξ ^ 2 : ℝ) : ℂ) * fourier ψ ξ := by
    rw [fourier_deriv hdi (hd.differentiable (by simp)) hddi,
      fourier_deriv (hψ.continuous.integrable_of_hasCompactSupport hc)
        (hψ.differentiable (by simp)) hdi]
    simp only [Complex.ofReal_pow]
    calc
      _ = (ξ : ℂ) ^ 2 * Complex.I ^ 2 * fourier ψ ξ := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hp := integral_fourier_pairing_of_compactSmooth hf hdd hc.deriv.deriv
  have heq : (∫ ξ : ℝ, (fourier f ξ * star (fourier (deriv (deriv ψ)) ξ)).re) =
      -(∫ ξ : ℝ, |ξ| * (fourier q ξ * star (fourier ψ ξ)).re) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact ae_of_all _ fun ξ => by
      dsimp only
      rw [hFd, hF]
      simp only [map_mul, map_neg, Complex.star_def, Complex.conj_ofReal,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
        zero_mul, mul_zero, sub_zero, zero_sub]
      rw [← sq_abs ξ]
      ring
  rw [heq] at hp
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hJ : (∫ ξ : ℝ, |ξ| * (fourier q ξ * star (fourier ψ ξ)).re) =
      -((2 * Real.pi) * ∫ x : ℝ, f x * deriv (deriv ψ) x) := by linarith [hp]
  change (1 / (2 * Real.pi)) *
    (∫ ξ : ℝ, |ξ| * (fourier q ξ * star (fourier ψ ξ)).re) = _
  rw [hJ]
  field_simp

end Torsion.Spectral

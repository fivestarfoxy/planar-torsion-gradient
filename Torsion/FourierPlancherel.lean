import Torsion.RestrictedSpectralForm
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Plancherel for the actual compact smooth Fourier core

This derives the source-normalized Parseval identity directly from mathlib's
Schwartz inversion and its proved Fourier bilinear Fubini identity. No new
Fourier axiom, transform, or library revision is introduced.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- Complex conjugation interchanges the forward and inverse Fourier
integrals in mathlib's normalization. -/
theorem mathlib_fourier_conj (f : ℝ → ℂ) (x : ℝ) :
    𝓕 (fun ξ => star (f ξ)) x = star (𝓕⁻ f x) := by
  rw [Real.fourierIntegral_eq', Real.fourierIntegralInv_eq', Complex.star_def,
    ← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    simp only [smul_eq_mul, Complex.star_def, map_mul, ← Complex.exp_conj,
      Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.ofReal_neg]
    congr 2
    push_cast
    ring

/-- Schwartz Plancherel, obtained from actual inversion and the actual
Fourier bilinear integral identity already available in mathlib 4.19. -/
theorem SchwartzMap_integral_norm_sq_fourier (S : 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, ‖𝓕 S ξ‖ ^ 2) = ∫ x : ℝ, ‖S x‖ ^ 2 := by
  let FS : 𝓢(ℝ, ℂ) := SchwartzMap.fourierTransformCLM ℂ S
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact real_inner_comm (x : ℝ) (y : ℝ)
  have hgc : Integrable (fun ξ : ℝ => star (𝓕 S ξ)) := by
    simpa only [Complex.conjCLE_apply, Complex.star_def] using
      (Complex.conjCLE.toContinuousLinearMap.integrable_comp (FS.integrable (μ := volume)))
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (L := innerₗ ℝ) (μ := volume) (ν := volume) (ContinuousLinearMap.mul ℂ ℂ)
    Real.continuous_fourierChar continuous_inner S.integrable hgc
  rw [hflip] at h
  change (∫ ξ : ℝ, 𝓕 S ξ * star (𝓕 S ξ)) =
    ∫ x : ℝ, S x * 𝓕 (fun ξ => star (𝓕 S ξ)) x at h
  have hinv := S.continuous.fourier_inversion S.integrable FS.integrable
  simp only [mathlib_fourier_conj, hinv] at h
  have hnorm (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.star_def, Complex.mul_conj]
  simp only [hnorm, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

/-- The source-normalized Fourier transform of a compact smooth real
function has an integrable squared norm. -/
theorem integrable_norm_sq_fourier_of_core {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun ξ : ℝ => ‖fourier f ξ‖ ^ 2) := by
  let S := compactSmoothSchwartz hf hc
  let FS : 𝓢(ℝ, ℂ) := SchwartzMap.fourierTransformCLM ℂ S
  have hi : Integrable (fun ξ : ℝ => ‖FS ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm FS.continuous.aestronglyMeasurable).mp
      (FS.memLp 2)
  have hp : 2 * Real.pi ≠ 0 := by positivity
  have hid := hi.comp_div hp
  simpa only [fourier_eq_mathlib] using hid

/-- Parseval with exactly the Fourier convention and `2π` factor of the
existing concrete restricted form. -/
theorem integral_norm_sq_fourier_of_core {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ ξ : ℝ, ‖fourier f ξ‖ ^ 2) =
      (2 * Real.pi) * ∫ x : ℝ, f x ^ 2 := by
  let S := compactSmoothSchwartz hf hc
  calc
    _ = ∫ ξ : ℝ, ‖𝓕 S (ξ / (2 * Real.pi))‖ ^ 2 := by
      simp only [fourier_eq_mathlib]
      rfl
    _ = (2 * Real.pi) * ∫ ξ : ℝ, ‖𝓕 S ξ‖ ^ 2 := by
      simpa only [smul_eq_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] using
        Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 S ξ‖ ^ 2) (2 * Real.pi)
    _ = (2 * Real.pi) * ∫ x : ℝ, f x ^ 2 := by
      rw [SchwartzMap_integral_norm_sq_fourier]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change ‖(f x : ℂ)‖ ^ 2 = f x ^ 2
        simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

end Torsion.Spectral

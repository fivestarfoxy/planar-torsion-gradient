module

public import Torsion.RestrictedSpectralForm
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
  rw [Real.fourier_eq', Real.fourierInv_eq', Complex.star_def,
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
  exact SchwartzMap.integral_norm_sq_fourier S

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
  have heq (ξ : ℝ) : fourier f ξ = FS (ξ / (2 * Real.pi)) :=
    fourier_eq_mathlib f ξ
  exact hid.congr (ae_of_all _ fun ξ =>
    congrArg (fun z : ℂ => ‖z‖ ^ 2) (heq ξ).symm)

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

import Torsion.RestrictedSpectralInterpolation

/-!
# Fourier interpolation for arbitrary compact smooth functions

Cauchy--Schwarz in the actual Fourier L² space, the proved source-normalized
Parseval identity, and the proved Fourier differentiation formula give the
usual interpolation inequality with all normalization factors cancelled.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace

namespace Torsion.Spectral

/-- The actual Fourier integral of every compact smooth function is L²,
without any restriction on the position of its support. -/
theorem fourier_memLp_of_compactSmooth {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : MemLp (fourier f) 2 volume :=
  (memLp_two_iff_integrable_sq_norm
    (fourier_continuous (hf.continuous.integrable_of_hasCompactSupport hc)).aestronglyMeasurable).mpr
      (integrable_norm_sq_fourier_of_core hf hc)

/-- Fourier interpolation for arbitrary genuinely compact smooth functions,
including supports which intersect or lie outside the original endpoints. -/
theorem energy_sq_le_integral_sq_mul_integral_deriv_sq_of_compactSmooth {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (energy f f) ^ 2 ≤ (∫ x : ℝ, f x ^ 2) * (∫ x : ℝ, (_root_.deriv f x) ^ 2) := by
  have hdf : ContDiff ℝ ∞ (_root_.deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hCS := integral_mul_sq_le_mul_integral_sq
    (fourier_memLp_of_compactSmooth hf hc).norm
    (fourier_memLp_of_compactSmooth hdf hc.deriv).norm
  have hproduct : (fun ξ : ℝ => ‖fourier f ξ‖ * ‖fourier (_root_.deriv f) ξ‖) =
      fun ξ : ℝ => |ξ| * ‖fourier f ξ‖ ^ 2 := by
    funext ξ
    rw [fourier_deriv (hf.continuous.integrable_of_hasCompactSupport hc)
      (hf.differentiable (by simp)) (hdf.continuous.integrable_of_hasCompactSupport hc.deriv),
      norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    ring
  simp only [hproduct] at hCS
  rw [integral_norm_sq_fourier_of_core hf hc,
    integral_norm_sq_fourier_of_core hdf hc.deriv] at hCS
  rw [energy_self, mul_pow]
  calc
    (1 / (2 * Real.pi)) ^ 2 * (∫ ξ : ℝ, |ξ| * ‖fourier f ξ‖ ^ 2) ^ 2 ≤
        (1 / (2 * Real.pi)) ^ 2 *
          (((2 * Real.pi) * ∫ x : ℝ, f x ^ 2) *
            ((2 * Real.pi) * ∫ x : ℝ, (_root_.deriv f x) ^ 2)) :=
      mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = _ := by
      field_simp [Real.pi_ne_zero]
      ring

end Torsion.Spectral

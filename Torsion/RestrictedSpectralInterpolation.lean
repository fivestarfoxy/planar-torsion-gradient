import Torsion.RestrictedSpectralParseval
import Torsion.RestrictedSpectralBoundaryPrimitive
import Mathlib.Data.Real.Sqrt

/-!
# Actual Fourier interpolation between L², half energy and one derivative

Cauchy--Schwarz in the actual Fourier L² space, the proved source-normalized
Parseval identity, and the proved Fourier differentiation formula give the
usual interpolation inequality with all normalization factors cancelled.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace

namespace Torsion.Spectral

/-- Cauchy--Schwarz for the actual real L² integrals, obtained from the
ordinary Hilbert-space inequality on their actual equivalence classes. -/
theorem integral_mul_sq_le_mul_integral_sq {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫ x : ℝ, f x * g x) ^ 2 ≤ (∫ x : ℝ, f x ^ 2) * (∫ x : ℝ, g x ^ 2) := by
  let u : Lp ℝ 2 (volume : Measure ℝ) := hf.toLp f
  let v : Lp ℝ 2 (volume : Measure ℝ) := hg.toLp g
  have hpair : ⟪u, v⟫_ℝ = ∫ x : ℝ, f x * g x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    simp only [u, v, hx, hy, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]
  have hselfu : ⟪u, u⟫_ℝ = ∫ x : ℝ, f x ^ 2 := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [u, hx, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm, pow_two]
  have hselfv : ⟪v, v⟫_ℝ = ∫ x : ℝ, g x ^ 2 := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    simp only [v, hx, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm, pow_two]
  have h := real_inner_mul_inner_self_le u v
  simpa only [hpair, hselfu, hselfv, pow_two] using h

/-- The source Fourier derivative has exactly the expected frequency
norm, with no extra 2π factor in this normalization. -/
theorem IsCore.norm_fourier_deriv {f : ℝ → ℝ} (hf : IsCore f) (ξ : ℝ) :
    ‖fourier (_root_.deriv f) ξ‖ = |ξ| * ‖fourier f ξ‖ := by
  rw [fourier_deriv hf.memRestrictedFormDomain.integrable (hf.1.differentiable (by simp)) hf.deriv.memRestrictedFormDomain.integrable,
    norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The genuine original half-Laplacian energy interpolates the actual
L² value and derivative norms on the original compact smooth core. -/
theorem IsCore.energy_sq_le_integral_sq_mul_integral_deriv_sq {f : ℝ → ℝ}
    (hf : IsCore f) :
    (energy f f) ^ 2 ≤ (∫ x : ℝ, f x ^ 2) * (∫ x : ℝ, (_root_.deriv f x) ^ 2) := by
  have hCS := integral_mul_sq_le_mul_integral_sq hf.fourier_memLp.norm hf.deriv.fourier_memLp.norm
  have hproduct : (fun ξ : ℝ => ‖fourier f ξ‖ * ‖fourier (_root_.deriv f) ξ‖) =
      fun ξ : ℝ => |ξ| * ‖fourier f ξ‖ ^ 2 := by
    funext ξ
    rw [hf.norm_fourier_deriv ξ]
    ring
  simp only [hproduct] at hCS
  rw [integral_norm_sq_fourier_of_core hf.1 hf.2.1,
    integral_norm_sq_fourier_of_core hf.deriv.1 hf.deriv.2.1] at hCS
  rw [energy_self, mul_pow]
  calc
    (1 / (2 * Real.pi)) ^ 2 * (∫ ξ : ℝ, |ξ| * ‖fourier f ξ‖ ^ 2) ^ 2 ≤
        (1 / (2 * Real.pi)) ^ 2 *
          (((2 * Real.pi) * ∫ x : ℝ, f x ^ 2) *
            ((2 * Real.pi) * ∫ x : ℝ, (_root_.deriv f x) ^ 2)) :=
      mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = (∫ x : ℝ, f x ^ 2) * (∫ x : ℝ, (_root_.deriv f x) ^ 2) := by
      field_simp [Real.pi_ne_zero]
      ring

/-- Square-root form of the same actual Fourier interpolation estimate. -/
theorem IsCore.energy_le_sqrt_integral_sq_mul_integral_deriv_sq {f : ℝ → ℝ}
    (hf : IsCore f) :
    energy f f ≤ Real.sqrt ((∫ x : ℝ, f x ^ 2) * (∫ x : ℝ, (_root_.deriv f x) ^ 2)) :=
  Real.le_sqrt_of_sq_le hf.energy_sq_le_integral_sq_mul_integral_deriv_sq

end Torsion.Spectral

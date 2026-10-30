module

public import Torsion.FourierHilbertKernel

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual height and the damped Hilbert multiplier

The Fourier primitive identity identifies the damped half-Laplacian of the
height with the damped Hilbert multiplier of the original odd density, with
the source's exact signs and constants.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- Exact pointwise multiplier identity, including frequency zero. -/
theorem dampedSignMultiplier_mul_fourier_height {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (y ξ : ℝ) :
    dampedSignMultiplier y ξ * fourier φ ξ =
      (Real.exp (-y * |ξ|) : ℂ) * ((|ξ| : ℝ) : ℂ) * fourier (height φ) ξ := by
  rw [fourier_height_identity hφ hodd hzero]
  unfold dampedSignMultiplier
  by_cases hξ : 0 < ξ
  · rw [if_pos hξ, abs_of_pos hξ]
    ring_nf
    simp only [Complex.I_sq]
    ring
  · rw [if_neg hξ, abs_of_nonpos (le_of_not_gt hξ)]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- Exact real integrand identity needed for the finite-energy pairing. -/
theorem dampedSignMultiplier_pairing_re_height {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (y ξ : ℝ) :
    (dampedSignMultiplier y ξ * fourier φ ξ * star (fourier ψ ξ)).re =
      Real.exp (-y * |ξ|) * (|ξ| *
        (fourier (height φ) ξ * star (fourier ψ ξ)).re) := by
  rw [dampedSignMultiplier_mul_fourier_height hφ hodd hzero]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
  ring

end Torsion.Spectral

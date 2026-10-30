import Torsion.SpectralScaling
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring

/-!
# Normalization invariance of the concrete spectral construction

This module proves the normalization-invariance clause of Theorem 1.1 for the
actual integrals and Cauchy image, without an abstract moment certificate.
The equalities require only a positive change of eigenfunction normalization.
They hold for the total formulas even before positivity of the spectral
moments, univalence, or the area interpretation has been established.
-/

noncomputable section
open Set

namespace Torsion.Spectral

/-- The exact candidate constant in (1.5), using the concrete moments (1.3). -/
def spectralConstant (a : ℝ) (φ : ℝ → ℝ) : ℝ :=
  Real.sqrt (squareMass φ / (2 * a * (mass φ) ^ 2))

/-- The area-normalized Cauchy image displayed in (1.5).
Identifying `a * squareMass φ / 2` with the physical area is separate. -/
def normalizedImage (a : ℝ) (φ : ℝ → ℝ) : Set ℂ :=
  (fun z : ℂ => (((Real.sqrt (a * squareMass φ / 2))⁻¹ : ℝ) : ℂ) * z) ''
    (cauchy φ '' upperHalfPlane)

/-- Nonzero rescaling leaves the concrete constant unchanged. -/
theorem spectralConstant_mul (a t : ℝ) (φ : ℝ → ℝ) (ht : t ≠ 0) :
    spectralConstant a (fun s => t * φ s) = spectralConstant a φ := by
  unfold spectralConstant
  rw [squareMass_mul, mass_mul]
  congr 1
  rw [show 2 * a * (t * mass φ) ^ 2 =
      t ^ 2 * (2 * a * (mass φ) ^ 2) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 ht)

/-- Compensation between Cauchy-image scaling and its normalizing factor. -/
theorem normalizing_factor_mul (a t : ℝ) (φ : ℝ → ℝ) (ht : 0 < t) :
    (Real.sqrt (a * squareMass (fun s => t * φ s) / 2))⁻¹ * t =
      (Real.sqrt (a * squareMass φ / 2))⁻¹ := by
  rw [squareMass_mul]
  rw [show a * (t ^ 2 * squareMass φ) / 2 =
      t ^ 2 * (a * squareMass φ / 2) by ring]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le,
    mul_inv_rev, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]

/-- The actual normalized Cauchy image is independent of the positive
normalization of the eigenfunction, as asserted in Theorem 1.1. -/
theorem normalizedImage_mul (a t : ℝ) (φ : ℝ → ℝ) (ht : 0 < t) :
    normalizedImage a (fun s => t * φ s) = normalizedImage a φ := by
  unfold normalizedImage
  rw [cauchy_image_mul, Set.image_image]
  apply Set.image_congr
  intro z hz
  change
    (((Real.sqrt (a * squareMass (fun s => t * φ s) / 2))⁻¹ : ℝ) : ℂ) *
        ((t : ℂ) * z) =
      (((Real.sqrt (a * squareMass φ / 2))⁻¹ : ℝ) : ℂ) * z
  rw [← mul_assoc, ← Complex.ofReal_mul, normalizing_factor_mul a t φ ht]

/-- Both concrete objects in (1.5) are unchanged by a positive normalization. -/
theorem normalization_invariance (a t : ℝ) (φ : ℝ → ℝ) (ht : 0 < t) :
    spectralConstant a (fun s => t * φ s) = spectralConstant a φ ∧
    normalizedImage a (fun s => t * φ s) = normalizedImage a φ :=
  ⟨spectralConstant_mul a t φ ht.ne', normalizedImage_mul a t φ ht⟩

end Torsion.Spectral

end

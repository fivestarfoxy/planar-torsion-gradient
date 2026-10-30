import Torsion.SpectralDefinitions
import Mathlib.Tactic.Ring

/-!
# Scaling of the concrete spectral construction

These identities apply directly to the integrals defining equations (1.2)–(1.4)
and (5.3). They hold for every real multiplier, including zero; the Bochner
integral's constant-multiple identity requires no separate integrability
hypothesis. Thus these are properties of the concrete definitions, rather than
assumptions about abstract moments.
-/

noncomputable section
open Set MeasureTheory

namespace Torsion.Spectral

/-- The integrated eigenfunction height scales linearly. -/
theorem height_mul (t : ℝ) (φ : ℝ → ℝ) (x : ℝ) :
    height (fun s => t * φ s) x = t * height φ x := by
  unfold height
  split_ifs
  · exact integral_const_mul t φ
  · simp

/-- The first moment `M` scales linearly with the eigenfunction. -/
theorem mass_mul (t : ℝ) (φ : ℝ → ℝ) :
    mass (fun s => t * φ s) = t * mass φ := by
  simp only [mass, height_mul, integral_const_mul]

/-- The second moment `N` scales quadratically with the eigenfunction. -/
theorem squareMass_mul (t : ℝ) (φ : ℝ → ℝ) :
    squareMass (fun s => t * φ s) = t ^ 2 * squareMass φ := by
  simp only [squareMass, height_mul, mul_pow, integral_const_mul]

/-- The Cauchy transform constructing the physical domain scales linearly. -/
theorem cauchy_mul (t : ℝ) (φ : ℝ → ℝ) (z : ℂ) :
    cauchy (fun s => t * φ s) z = (t : ℂ) * cauchy φ z := by
  simp only [cauchy, height_mul, Complex.ofReal_mul, mul_div_assoc, integral_const_mul]
  ring

/-- In particular, the constructed image domain is multiplied by the same
complex scalar. No univalence or boundary regularity is needed for this identity. -/
theorem cauchy_image_mul (t : ℝ) (φ : ℝ → ℝ) (S : Set ℂ) :
    cauchy (fun s => t * φ s) '' S =
      (fun w : ℂ => (t : ℂ) * w) '' (cauchy φ '' S) := by
  rw [Set.image_image]
  apply Set.image_congr
  intro z hz
  exact cauchy_mul t φ z

/-- The auxiliary Cauchy transform scales quadratically. -/
theorem auxiliary_mul (t : ℝ) (φ : ℝ → ℝ) (z : ℂ) :
    auxiliary (fun s => t * φ s) z = (t : ℂ) ^ 2 * auxiliary φ z := by
  simp only [auxiliary, height_mul, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow,
    mul_div_assoc, integral_const_mul]
  ring

end Torsion.Spectral

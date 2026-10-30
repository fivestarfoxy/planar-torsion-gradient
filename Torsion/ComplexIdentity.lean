import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algebra in the holomorphic and boundary-gradient identities

These are algebraic parts of Lemmas 5.2 and 7.1. They do not prove the
Cauchy boundary-value theorem, holomorphic uniqueness, or univalence.
In particular, division by the derivative is used only with the explicit
hypothesis that the derivative is nonzero, as required by the proof order
in the writeup.
-/

namespace Torsion.ComplexIdentity

noncomputable section

/-- The right-hand side of the holomorphic identity (5.4). -/
def holomorphicRHS (a b : ℝ) (f' : ℂ) : ℂ :=
  ((b / a : ℝ) : ℂ) * f' - f' ^ 2 / ((2 * a : ℝ) : ℂ)

/-- The derivative of the physical holomorphic function, once division is justified. -/
def physicalDerivative (a b : ℝ) (f' : ℂ) : ℂ :=
  ((b / a : ℝ) : ℂ) - f' / ((2 * a : ℝ) : ℂ)

/-- The boundary imaginary parts agree in Lemma 5.2. -/
theorem boundary_imag_identity (a b Y v Y' : ℝ) (ha : a ≠ 0)
    (hv : v = b - a * Y) :
    (holomorphicRHS a b ((v : ℂ) + (Y' : ℂ) * Complex.I)).im = Y * Y' := by
  simp only [holomorphicRHS, Complex.sub_im, Complex.mul_im, Complex.div_ofReal_im,
    pow_two, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.mul_re]
  rw [hv]
  field_simp [ha]
  ring

/-- Canceling the derivative in (5.4) is valid only after proving it is nonzero. -/
theorem quotient_identity (a b : ℝ) (A' f' : ℂ) (hf : f' ≠ 0)
    (hA : A' = holomorphicRHS a b f') :
    A' / f' = physicalDerivative a b f' := by
  rw [hA]
  unfold holomorphicRHS physicalDerivative
  field_simp [hf]
  ring

/-- The horizontal component of the torsion gradient in Lemma 7.1. -/
theorem boundary_gradient_horizontal (a b v φ : ℝ) :
    (physicalDerivative a b ((v : ℂ) - (φ : ℂ) * Complex.I)).im = φ / (2 * a) := by
  simp only [physicalDerivative, Complex.sub_im, Complex.ofReal_im,
    Complex.div_ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re]
  ring

/-- The vertical component uses the linear boundary equation `v = b - a Y`. -/
theorem boundary_gradient_vertical (a b Y v φ : ℝ) (ha : a ≠ 0)
    (hv : v = b - a * Y) :
    -Y + (physicalDerivative a b ((v : ℂ) - (φ : ℂ) * Complex.I)).re =
      v / (2 * a) := by
  simp only [physicalDerivative, Complex.sub_re, Complex.div_ofReal_re,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [hv]
  field_simp [ha]
  ring

/-- The complex gradient is the positively rotated tangent divided by `2a`. -/
theorem boundary_gradient_complex (a v φ : ℝ) :
    ((φ / (2 * a) : ℝ) : ℂ) + ((v / (2 * a) : ℝ) : ℂ) * Complex.I =
      Complex.I * ((v : ℂ) - (φ : ℂ) * Complex.I) / ((2 * a : ℝ) : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_div, div_mul_eq_mul_div, ← add_div]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- Norm of the boundary gradient, the algebraic content of (7.3). -/
theorem boundary_gradient_norm (a v φ : ℝ) (ha : 0 < a) :
    ‖((φ / (2 * a) : ℝ) : ℂ) + ((v / (2 * a) : ℝ) : ℂ) * Complex.I‖ =
      ‖(v : ℂ) - (φ : ℂ) * Complex.I‖ / (2 * a) := by
  rw [boundary_gradient_complex, norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) ha)]

end

end Torsion.ComplexIdentity

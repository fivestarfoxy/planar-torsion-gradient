import Torsion.SpectralPositivity
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Parity of the actual height derivative

The height in the original definition is even. Differentiation reverses
its parity, including at points where the totalized derivative is zero.
The zero exterior restriction preserves that odd parity. No exterior
smoothness of a spectral representative is required.
-/

noncomputable section
open Set

namespace Torsion.Spectral

/-- The ordinary totalized derivative of an even real function is odd.
This also holds at nondifferentiability points, since reflection preserves
nondifferentiability and both totalized derivatives then vanish. -/
theorem deriv_odd_of_even {H : ℝ → ℝ} (hEven : Function.Even H) :
    Function.Odd (_root_.deriv H) := by
  intro x
  have hcomp : (fun y : ℝ => H (-y)) = H := funext hEven
  have h := deriv_comp_neg H x
  rw [hcomp] at h
  linarith

/-- Zero restriction of the negative height derivative to the open
spectral interval is odd. The theorem needs no global differentiability. -/
theorem piecewise_neg_deriv_even_odd {H : ℝ → ℝ} (hEven : Function.Even H) :
    Function.Odd (fun x : ℝ => if |x| < 1 then -_root_.deriv H x else 0) := by
  intro x
  simp only [abs_neg]
  split_ifs
  · rw [deriv_odd_of_even hEven x]
  · simp

/-- Parity for the actual integrated profile of an arbitrary density. -/
theorem piecewise_neg_deriv_height_odd (f : ℝ → ℝ) :
    Function.Odd (fun x : ℝ => if |x| < 1 then -_root_.deriv (height f) x else 0) :=
  piecewise_neg_deriv_even_odd (height_even f)

end Torsion.Spectral

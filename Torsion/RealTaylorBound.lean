module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform quadratic remainder on an actual real segment

Two applications of the ordinary mean-value estimate give the normal-line
quadratic error needed for fixed-ball harmonic representatives. The bound
uses an explicit supremum for the actual second derivative; it does not
assume uniform convergence of boundary derivatives.
-/

noncomputable section
open Set
open scoped ContDiff

namespace Torsion

/-- An actual bound for the second derivative on `[0,h]` controls the
linear Taylor remainder there. The nonsharp coefficient `C` is convenient
for uniform families and requires no integral remainder infrastructure. -/
theorem abs_sub_linear_le_sq_of_second_deriv_bound
    {f : ℝ → ℝ} {C h : ℝ}
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (deriv f))
    (hC : 0 ≤ C) (hh : 0 ≤ h)
    (hbound : ∀ x ∈ Icc 0 h, |deriv (deriv f) x| ≤ C) :
    |f h - f 0 - deriv f 0 * h| ≤ C * h ^ 2 := by
  have hvariation (x : ℝ) (hx : x ∈ Icc 0 h) :
      |deriv f x - deriv f 0| ≤ C * x := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := (0 : ℝ)) (b := h) (f := deriv f) (f' := deriv (deriv f))
      (fun y _ => (hdf y).hasDerivAt.hasDerivWithinAt)
      (fun y hy => by
        simpa only [Real.norm_eq_abs] using hbound y ⟨hy.1, hy.2.le⟩) x hx
    simpa only [Real.norm_eq_abs, sub_zero] using h
  let F : ℝ → ℝ := fun x => f x - f 0 - deriv f 0 * x
  have hF (x : ℝ) : HasDerivAt F (deriv f x - deriv f 0) x := by
    convert ((hf x).hasDerivAt.sub_const (f 0)).sub
      ((hasDerivAt_id x).const_mul (deriv f 0)) using 1 <;>
      simp [F]
    funext y
    rfl
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := h) (f := F) (f' := fun x => deriv f x - deriv f 0)
    (fun x _ => (hF x).hasDerivWithinAt)
    (C := C * h)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      exact (hvariation x ⟨hx.1, hx.2.le⟩).trans
        (mul_le_mul_of_nonneg_left hx.2.le hC)) h ⟨hh, le_rfl⟩
  simpa [F, Real.norm_eq_abs, pow_two, mul_assoc] using h

/-- Smooth normal-line functions satisfy the same explicit quadratic bound. -/
theorem abs_sub_linear_le_sq_of_contDiff_second_deriv_bound
    {f : ℝ → ℝ} {C h : ℝ} (hf : ContDiff ℝ ∞ f)
    (hC : 0 ≤ C) (hh : 0 ≤ h)
    (hbound : ∀ x ∈ Icc 0 h, |deriv (deriv f) x| ≤ C) :
    |f h - f 0 - deriv f 0 * h| ≤ C * h ^ 2 := by
  exact Torsion.abs_sub_linear_le_sq_of_second_deriv_bound
    (hf.differentiable (by simp))
    ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) hC hh hbound

/-- Dividing by the positive normal distance gives a uniform first-order
bound for the boundary quotient. -/
theorem abs_quotient_sub_deriv_le_of_second_deriv_bound
    {f : ℝ → ℝ} {C h : ℝ}
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (deriv f))
    (hC : 0 ≤ C) (hh : 0 < h)
    (hbound : ∀ x ∈ Icc 0 h, |deriv (deriv f) x| ≤ C) :
    |(f h - f 0) / h - deriv f 0| ≤ C * h := by
  have heq : (f h - f 0) / h - deriv f 0 =
      (f h - f 0 - deriv f 0 * h) / h := by
    field_simp
  rw [heq, abs_div, abs_of_pos hh]
  apply (div_le_iff₀ hh).mpr
  exact (abs_sub_linear_le_sq_of_second_deriv_bound hf hdf hC hh.le hbound).trans_eq
    (by ring)

/-- Smooth zero-boundary normal lines have a quotient error at most `C h`. -/
theorem abs_quotient_sub_deriv_le_of_contDiff_second_deriv_bound
    {f : ℝ → ℝ} {C h : ℝ} (hf : ContDiff ℝ ∞ f)
    (hC : 0 ≤ C) (hh : 0 < h)
    (hbound : ∀ x ∈ Icc 0 h, |deriv (deriv f) x| ≤ C) :
    |(f h - f 0) / h - deriv f 0| ≤ C * h := by
  exact Torsion.abs_quotient_sub_deriv_le_of_second_deriv_bound
    (hf.differentiable (by simp))
    ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) hC hh hbound

/-- The operator-norm version matches bounds obtained by differentiating a
fixed convolution kernel along the normal line. -/
theorem abs_quotient_sub_deriv_le_of_contDiff_second_fderiv_bound
    {f : ℝ → ℝ} {C h : ℝ} (hf : ContDiff ℝ ∞ f)
    (hC : 0 ≤ C) (hh : 0 < h)
    (hbound : ∀ x ∈ Icc 0 h, ‖fderiv ℝ (deriv f) x‖ ≤ C) :
    |(f h - f 0) / h - deriv f 0| ≤ C * h := by
  apply abs_quotient_sub_deriv_le_of_contDiff_second_deriv_bound hf hC hh
  intro x hx
  simpa only [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs] using hbound x hx

/-- A single second-derivative bound on a fixed segment gives the quotient
estimate uniformly at every smaller positive normal distance. -/
theorem abs_quotient_sub_deriv_le_uniform
    {f : ℝ → ℝ} {C R : ℝ} (hf : ContDiff ℝ ∞ f) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Icc 0 R, |deriv (deriv f) x| ≤ C)
    {h : ℝ} (hh : 0 < h) (hhR : h ≤ R) :
    |(f h - f 0) / h - deriv f 0| ≤ C * h := by
  apply abs_quotient_sub_deriv_le_of_contDiff_second_deriv_bound hf hC hh
  intro x hx
  exact hbound x ⟨hx.1, hx.2.trans hhR⟩

end Torsion

module

public import Torsion.CauchyTransformIntegrationByParts
public import Torsion.CauchyTransformPoisson
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Concrete noncriticality of the Cauchy map

Pairing the odd density at `s` and `-s` determines the sign of the
imaginary part of `F'` on either side of the imaginary axis. On the axis
its real part is strictly negative. These statements concern the actual
Cauchy integral and do not assume univalence or a Jordan boundary theorem.
-/

noncomputable section
open Set MeasureTheory

namespace Torsion.Spectral

private theorem denominator_ne_zero {z : ℂ} (hz : z ∈ upperHalfPlane) (s : ℝ) :
    z - (s : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
  exact hz.ne' hi

/-- Pair the two halves of the actual symmetric integration interval. -/
theorem integral_Icc_symmetric_pair {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ s in Icc (-1 : ℝ) 1, f s) = ∫ s in (0 : ℝ)..1, f s + f (-s) := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  have hsplit : (∫ s in (-1 : ℝ)..0, f s) + (∫ s in (0 : ℝ)..1, f s) =
      ∫ s in (-1 : ℝ)..1, f s := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-1) 0) (hf.intervalIntegrable 0 1)
  have hneg : (∫ s in (-1 : ℝ)..0, f s) = ∫ s in (0 : ℝ)..1, f (-s) := by
    simpa only [neg_zero] using
      (intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := (1 : ℝ))).symm
  rw [← hsplit, hneg, add_comm]
  exact (intervalIntegral.integral_add (hf.intervalIntegrable 0 1)
      ((hf.comp continuous_neg).intervalIntegrable 0 1)).symm

/-- The odd Poisson density paired over the positive half interval. -/
theorem odd_poisson_integral_pair {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ) {x y : ℝ} (hy : 0 < y) :
    (∫ s in Icc (-1 : ℝ) 1, φ s / ((x - s) ^ 2 + y ^ 2)) =
      ∫ s in (0 : ℝ)..1,
        φ s * (1 / ((x - s) ^ 2 + y ^ 2) - 1 / ((x + s) ^ 2 + y ^ 2)) := by
  have hc : Continuous (fun s : ℝ => φ s / ((x - s) ^ 2 + y ^ 2)) :=
    hφ.div (by fun_prop) (fun s => ne_of_gt (by positivity))
  rw [integral_Icc_symmetric_pair hc]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [hodd s]
  simp only [sub_neg_eq_add]
  ring

/-- For a positive odd density the paired Poisson integral is strictly
positive to the right of the imaginary axis. -/
theorem odd_poisson_integral_pos {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < ∫ s in Icc (-1 : ℝ) 1, φ s / ((x - s) ^ 2 + y ^ 2) := by
  rw [odd_poisson_integral_pair hφ hodd hy]
  have hcm : Continuous (fun s : ℝ => 1 / ((x - s) ^ 2 + y ^ 2)) :=
    continuous_const.div (by fun_prop) (fun s => ne_of_gt (by positivity))
  have hcp : Continuous (fun s : ℝ => 1 / ((x + s) ^ 2 + y ^ 2)) :=
    continuous_const.div (by fun_prop) (fun s => ne_of_gt (by positivity))
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((hφ.mul (hcm.sub hcp)).intervalIntegrable 0 1) _ (by norm_num)
  intro s hs
  apply mul_pos (hpos s hs)
  apply sub_pos.2
  apply one_div_lt_one_div_of_lt (by positivity : 0 < (x - s) ^ 2 + y ^ 2)
  nlinarith [mul_pos hx hs.1]

/-- The imaginary derivative is the negative odd Poisson integral. -/
theorem cauchy_derivative_im_eq {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (deriv (cauchy φ) z).im = -(Real.pi⁻¹ * z.im) *
      ∫ s in Icc (-1 : ℝ) 1, φ s / ((z.re - s) ^ 2 + z.im ^ 2) := by
  rw [deriv_cauchy_eq_eigenfunction_integral hφ hodd hzero hz]
  have hint : IntegrableOn (fun s : ℝ => (φ s : ℂ) / (z - (s : ℂ)))
      (Icc (-1 : ℝ) 1) :=
    ((Complex.continuous_ofReal.comp hφ).div
      (continuous_const.sub Complex.continuous_ofReal) (denominator_ne_zero hz)).integrableOn_Icc
  rw [← integral_const_mul]
  have him : (∫ s in Icc (-1 : ℝ) 1,
      ((Real.pi : ℂ)⁻¹) * ((φ s : ℂ) / (z - (s : ℂ)))).im =
      ∫ s in Icc (-1 : ℝ) 1,
      (((Real.pi : ℂ)⁻¹) * ((φ s : ℂ) / (z - (s : ℂ)))).im :=
    (integral_im (hint.const_mul ((Real.pi : ℂ)⁻¹))).symm
  rw [him, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s _
  rw [← Complex.ofReal_inv]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_im,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply, zero_mul, zero_div,
    sub_zero, zero_sub]
  ring

/-- No critical point can lie in the right half of H: the imaginary part
of the actual complex derivative is strictly negative there. -/
theorem cauchy_derivative_im_neg_of_re_pos {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ upperHalfPlane) (hx : 0 < z.re) :
    (deriv (cauchy φ) z).im < 0 := by
  rw [cauchy_derivative_im_eq hφ hodd hzero hz]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (inv_pos.2 Real.pi_pos) hz))
    (odd_poisson_integral_pos hφ hodd hpos hx hz)

/-- The odd Poisson integral changes sign when the horizontal coordinate
is reflected. -/
theorem odd_poisson_integral_neg_horizontal {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ) {x y : ℝ} (hy : 0 < y) :
    (∫ s in Icc (-1 : ℝ) 1, φ s / ((-x - s) ^ 2 + y ^ 2)) =
      -(∫ s in Icc (-1 : ℝ) 1, φ s / ((x - s) ^ 2 + y ^ 2)) := by
  rw [odd_poisson_integral_pair hφ hodd hy,
    odd_poisson_integral_pair hφ hodd hy, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  have hm : (-x - s) ^ 2 + y ^ 2 = (x + s) ^ 2 + y ^ 2 := by ring
  have hp : (-x + s) ^ 2 + y ^ 2 = (x - s) ^ 2 + y ^ 2 := by ring
  rw [hm, hp]
  ring

theorem cauchy_derivative_im_pos_of_re_neg {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ upperHalfPlane) (hx : z.re < 0) :
    0 < (deriv (cauchy φ) z).im := by
  rw [cauchy_derivative_im_eq hφ hodd hzero hz]
  have hp := odd_poisson_integral_pos hφ hodd hpos (neg_pos.2 hx) hz
  have hr := odd_poisson_integral_neg_horizontal hφ hodd (x := -z.re) hz
  simp only [neg_neg] at hr
  rw [hr]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos (mul_pos (inv_pos.2 Real.pi_pos) hz))
    (neg_neg_of_pos hp)

/-- The real part of the derivative is also the actual differentiated
integral, with the standard real Cauchy kernel. -/
theorem cauchy_derivative_re_eq {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (deriv (cauchy φ) z).re = Real.pi⁻¹ *
      ∫ s in Icc (-1 : ℝ) 1, φ s * (z.re - s) / ((z.re - s) ^ 2 + z.im ^ 2) := by
  rw [deriv_cauchy_eq_eigenfunction_integral hφ hodd hzero hz]
  have hint : IntegrableOn (fun s : ℝ => (φ s : ℂ) / (z - (s : ℂ)))
      (Icc (-1 : ℝ) 1) :=
    ((Complex.continuous_ofReal.comp hφ).div
      (continuous_const.sub Complex.continuous_ofReal) (denominator_ne_zero hz)).integrableOn_Icc
  rw [← integral_const_mul]
  have hre : (∫ s in Icc (-1 : ℝ) 1,
      ((Real.pi : ℂ)⁻¹) * ((φ s : ℂ) / (z - (s : ℂ)))).re =
      ∫ s in Icc (-1 : ℝ) 1,
      (((Real.pi : ℂ)⁻¹) * ((φ s : ℂ) / (z - (s : ℂ)))).re :=
    (integral_re (hint.const_mul ((Real.pi : ℂ)⁻¹))).symm
  rw [hre, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s _
  rw [← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.div_re,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply, zero_mul, mul_zero,
    zero_div, sub_zero, add_zero]
  ring

/-- On the imaginary axis the actual complex derivative is strictly
negative in its real part. This treats the line missed by the two strict
imaginary-part inequalities. -/
theorem cauchy_derivative_re_neg_of_re_zero {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ upperHalfPlane) (hx : z.re = 0) :
    (deriv (cauchy φ) z).re < 0 := by
  have hzi : 0 < z.im := hz
  rw [cauchy_derivative_re_eq hφ hodd hzero hz, hx]
  have hc : Continuous (fun s : ℝ => φ s * (0 - s) / ((0 - s) ^ 2 + z.im ^ 2)) :=
    (hφ.mul (continuous_const.sub continuous_id)).div (by fun_prop)
      (fun s => ne_of_gt (by positivity : 0 < (0 - s) ^ 2 + z.im ^ 2))
  have heq : (∫ s in Icc (-1 : ℝ) 1, φ s * (0 - s) / ((0 - s) ^ 2 + z.im ^ 2)) =
      -(∫ s in (0 : ℝ)..1, 2 * s * φ s / (s ^ 2 + z.im ^ 2)) := by
    rw [integral_Icc_symmetric_pair hc, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [hodd s]
    simp only [zero_sub, neg_neg, neg_sq]
    ring
  rw [heq]
  apply mul_neg_of_pos_of_neg (inv_pos.2 Real.pi_pos)
  apply neg_neg_of_pos
  have hci : Continuous (fun s : ℝ => 2 * s * φ s / (s ^ 2 + z.im ^ 2)) :=
    ((continuous_const.mul continuous_id).mul hφ).div (by fun_prop)
      (fun s => ne_of_gt (by positivity : 0 < s ^ 2 + z.im ^ 2))
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (hci.intervalIntegrable 0 1) _
    (by norm_num)
  intro s hs
  exact div_pos (mul_pos (mul_pos (by norm_num) hs.1) (hpos s hs)) (by positivity)

/-- The concrete Cauchy transform has no interior critical point. The proof
uses only the odd, positive profile and the actual integral formulas;
univalence and convexity are not hypotheses. -/
theorem cauchy_derivative_ne_zero {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    deriv (cauchy φ) z ≠ 0 := by
  intro heq
  rcases lt_trichotomy z.re 0 with hx | hx | hx
  · have h := cauchy_derivative_im_pos_of_re_neg hφ hodd hzero hpos hz hx
    exact h.ne' (by simpa only [Complex.zero_im] using congrArg Complex.im heq)
  · have h := cauchy_derivative_re_neg_of_re_zero hφ hodd hzero hpos hz hx
    exact h.ne (by simpa only [Complex.zero_re] using congrArg Complex.re heq)
  · have h := cauchy_derivative_im_neg_of_re_pos hφ hodd hzero hpos hz hx
    exact h.ne (by simpa only [Complex.zero_im] using congrArg Complex.im heq)

end Torsion.Spectral

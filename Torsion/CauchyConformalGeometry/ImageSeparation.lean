import Torsion.CauchyConformalGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Separation of the two halves of the concrete Cauchy image

Integration by parts against the real logarithm gives a nonsingular
representation of the real part in terms of the odd density. The two
horizontal halves of H have images on opposite sides of the imaginary
axis. No boundary trace or Jordan theorem is assumed.
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

theorem cauchy_re_eq {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (cauchy φ z).re = -Real.pi⁻¹ * ∫ s in Icc (-1 : ℝ) 1,
      height φ s * (z.re - s) / ((z.re - s) ^ 2 + z.im ^ 2) := by
  have hint : IntegrableOn (fun s : ℝ => (height φ s : ℂ) / (z - (s : ℂ)))
      (Icc (-1 : ℝ) 1) :=
    ((Complex.continuous_ofReal.comp (height_continuous hφ)).div
      (continuous_const.sub Complex.continuous_ofReal) (denominator_ne_zero hz)).integrableOn_Icc
  unfold cauchy
  rw [← integral_const_mul]
  have hre : (∫ s in Icc (-1 : ℝ) 1,
      -((Real.pi : ℂ)⁻¹) * ((height φ s : ℂ) / (z - (s : ℂ)))).re =
      ∫ s in Icc (-1 : ℝ) 1,
      (-((Real.pi : ℂ)⁻¹) * ((height φ s : ℂ) / (z - (s : ℂ)))).re :=
    (integral_re (hint.const_mul (-((Real.pi : ℂ)⁻¹)))).symm
  rw [hre, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s _
  rw [← Complex.ofReal_inv, ← Complex.ofReal_neg]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.div_re,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply, zero_mul, mul_zero,
    zero_div, sub_zero, add_zero]
  ring

/-- Real integration by parts replaces the integrated profile with the odd
density in a logarithmic kernel. The denominator stays strictly positive
because the point lies above the real axis. -/
theorem height_log_integrationByParts {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {x y : ℝ} (hy : 0 < y) :
    (∫ s in Icc (-1 : ℝ) 1, height φ s * (x - s) / ((x - s) ^ 2 + y ^ 2)) =
      -(1 / 2 : ℝ) * ∫ s in Icc (-1 : ℝ) 1, φ s * Real.log ((x - s) ^ 2 + y ^ 2) := by
  let D : ℝ → ℝ := fun s => (x - s) ^ 2 + y ^ 2
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hDp (s : ℝ) : 0 < D s := by dsimp [D]; positivity
  have hlog : Continuous (fun s => Real.log (D s)) := hD.log (fun s => (hDp s).ne')
  let g : ℝ → ℝ := fun s => height φ s * Real.log (D s)
  let gp : ℝ → ℝ := fun s => -(φ s * Real.log (D s)) -
    2 * (height φ s * (x - s) / D s)
  have hgpk : Continuous (fun s => height φ s * (x - s) / D s) :=
    ((height_continuous hφ.continuousOn).mul (continuous_const.sub continuous_id)).div
      hD (fun s => (hDp s).ne')
  have hgp : Continuous gp := (hφ.mul hlog).neg.sub (continuous_const.mul hgpk)
  have hd : ∀ s : ℝ, HasDerivAt g (gp s) s := by
    intro s
    have hDs : HasDerivAt D (-2 * (x - s)) s := by
      convert (((hasDerivAt_const s x).sub (hasDerivAt_id s)).pow 2).add_const (y ^ 2) using 1
      simp [D]
    have h := (hasDerivAt_height hφ hodd hzero s).mul (hDs.log (hDp s).ne')
    convert h using 1
    dsimp [gp]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hgp.intervalIntegrable (-1) 1)
  have hp : height φ (1 : ℝ) = 0 := height_zero_of_one_le_abs φ (by norm_num)
  have hm : height φ (-1 : ℝ) = 0 := height_zero_of_one_le_abs φ (by norm_num)
  simp only [g, hp, hm, zero_mul, sub_self] at hi
  have heq : -(∫ s in (-1 : ℝ)..1, φ s * Real.log (D s)) -
      2 * (∫ s in (-1 : ℝ)..1, height φ s * (x - s) / D s) = 0 := by
    simpa only [gp, intervalIntegral.integral_sub
      ((hφ.mul hlog).neg.intervalIntegrable (-1) 1)
      ((continuous_const.mul hgpk).intervalIntegrable (-1) 1),
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] using hi
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  dsimp [D] at heq
  linarith

theorem cauchy_re_eq_log_integral {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (cauchy φ z).re = (Real.pi⁻¹ / 2) *
      ∫ s in Icc (-1 : ℝ) 1, φ s * Real.log ((z.re - s) ^ 2 + z.im ^ 2) := by
  rw [cauchy_re_eq hφ.continuousOn hz, height_log_integrationByParts hφ hodd hzero hz]
  ring

theorem odd_log_integral_pair {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ) {x y : ℝ} (hy : 0 < y) :
    (∫ s in Icc (-1 : ℝ) 1, φ s * Real.log ((x - s) ^ 2 + y ^ 2)) =
      ∫ s in (0 : ℝ)..1, φ s *
        (Real.log ((x - s) ^ 2 + y ^ 2) - Real.log ((x + s) ^ 2 + y ^ 2)) := by
  have hlog : Continuous (fun s : ℝ => Real.log ((x - s) ^ 2 + y ^ 2)) :=
    (by fun_prop : Continuous (fun s : ℝ => (x - s) ^ 2 + y ^ 2)).log
      (fun s => ne_of_gt (by positivity))
  rw [integral_Icc_symmetric_pair (hφ.mul hlog)]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [hodd s]
  simp only [sub_neg_eq_add]
  ring

/-- Points to the right of the imaginary axis have strictly negative real
image. This is an interior integral estimate, independent of any boundary
extension or univalence theorem. -/
theorem cauchy_re_neg_of_re_pos {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ upperHalfPlane) (hx : 0 < z.re) :
    (cauchy φ z).re < 0 := by
  have hy : 0 < z.im := hz
  rw [cauchy_re_eq_log_integral hφ hodd hzero hz, odd_log_integral_pair hφ hodd hy]
  apply mul_neg_of_pos_of_neg (by positivity : 0 < Real.pi⁻¹ / 2)
  have hcm : Continuous (fun s : ℝ => Real.log ((z.re - s) ^ 2 + z.im ^ 2)) :=
    (by fun_prop : Continuous (fun s : ℝ => (z.re - s) ^ 2 + z.im ^ 2)).log
      (fun s => ne_of_gt (by positivity))
  have hcp : Continuous (fun s : ℝ => Real.log ((z.re + s) ^ 2 + z.im ^ 2)) :=
    (by fun_prop : Continuous (fun s : ℝ => (z.re + s) ^ 2 + z.im ^ 2)).log
      (fun s => ne_of_gt (by positivity))
  have hposint : 0 < ∫ s in (0 : ℝ)..1,
      -(φ s * (Real.log ((z.re - s) ^ 2 + z.im ^ 2) -
        Real.log ((z.re + s) ^ 2 + z.im ^ 2))) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hφ.mul (hcm.sub hcp)).neg.intervalIntegrable 0 1) _ (by norm_num)
    intro s hs
    apply neg_pos.2
    apply mul_neg_of_pos_of_neg (hpos s hs)
    apply sub_neg.2
    apply Real.log_lt_log (by positivity : 0 < (z.re - s) ^ 2 + z.im ^ 2)
    nlinarith [mul_pos hx hs.1]
  rw [intervalIntegral.integral_neg] at hposint
  linarith

theorem odd_log_integral_neg_horizontal {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ) {x y : ℝ} (hy : 0 < y) :
    (∫ s in Icc (-1 : ℝ) 1, φ s * Real.log ((-x - s) ^ 2 + y ^ 2)) =
      -(∫ s in Icc (-1 : ℝ) 1, φ s * Real.log ((x - s) ^ 2 + y ^ 2)) := by
  rw [odd_log_integral_pair hφ hodd hy,
    odd_log_integral_pair hφ hodd hy, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  have hm : (-x - s) ^ 2 + y ^ 2 = (x + s) ^ 2 + y ^ 2 := by ring
  have hp : (-x + s) ^ 2 + y ^ 2 = (x - s) ^ 2 + y ^ 2 := by ring
  rw [hm, hp]
  ring

/-- Horizontal reflection reverses the real part of the actual Cauchy map. -/
theorem cauchy_re_neg_conj {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (cauchy φ (-star z)).re = -(cauchy φ z).re := by
  have hw : -star z ∈ upperHalfPlane := by simpa only [upperHalfPlane, mem_setOf_eq,
    Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg] using hz
  rw [cauchy_re_eq_log_integral hφ hodd hzero hw,
    cauchy_re_eq_log_integral hφ hodd hzero hz]
  simp only [Complex.neg_re, Complex.neg_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, neg_neg]
  rw [odd_log_integral_neg_horizontal hφ hodd hz]
  ring

/-- The left half has positive real image, complementary to the strict
negative image of the right half. -/
theorem cauchy_re_pos_of_re_neg {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ upperHalfPlane) (hx : z.re < 0) :
    0 < (cauchy φ z).re := by
  have hw : -star z ∈ upperHalfPlane := by simpa only [upperHalfPlane, mem_setOf_eq,
    Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg] using hz
  have hwr : 0 < (-star z).re := by simpa using neg_pos.2 hx
  have hn := cauchy_re_neg_of_re_pos hφ hodd hzero hpos hw hwr
  rw [cauchy_re_neg_conj hφ hodd hzero hz] at hn
  linarith

theorem cauchy_re_zero_of_re_zero {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) (hx : z.re = 0) :
    (cauchy φ z).re = 0 := by
  rw [cauchy_re_eq_log_integral hφ hodd hzero hz,
    odd_log_integral_pair hφ hodd hz, hx]
  simp only [zero_sub, zero_add, neg_sq, sub_self, mul_zero,
    intervalIntegral.integral_zero]

/-- The imaginary axis is exactly the preimage of the imaginary axis in H. -/
theorem cauchy_re_eq_zero_iff {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (cauchy φ z).re = 0 ↔ z.re = 0 := by
  constructor
  · intro heq
    rcases lt_trichotomy z.re 0 with hx | hx | hx
    · exact False.elim ((cauchy_re_pos_of_re_neg hφ hodd hzero hpos hz hx).ne' heq)
    · exact hx
    · exact False.elim ((cauchy_re_neg_of_re_pos hφ hodd hzero hpos hz hx).ne heq)
  · exact cauchy_re_zero_of_re_zero hφ hodd hzero hz

end Torsion.Spectral

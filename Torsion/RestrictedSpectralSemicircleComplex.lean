module

public import Torsion.RestrictedSpectralSemicircle
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The holomorphic square-root branch for the semicircle barrier

The square root on the closed upper half-plane is constructed from its
explicit real and imaginary parts. Its product at `z-1` and `z+1` is the
branch of `sqrt (z²-1)` which behaves like `z` at infinity.
-/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace Torsion.Spectral

/-- The principal square root on the closed upper half-plane, written
using ordinary real square roots so continuity includes the negative axis. -/
def upperSquareRoot (z : ℂ) : ℂ :=
  (Real.sqrt ((‖z‖ + z.re) / 2) : ℂ) +
    (Real.sqrt ((‖z‖ - z.re) / 2) : ℂ) * Complex.I

@[simp] theorem upperSquareRoot_re (z : ℂ) :
    (upperSquareRoot z).re = Real.sqrt ((‖z‖ + z.re) / 2) := by simp [upperSquareRoot]

@[simp] theorem upperSquareRoot_im (z : ℂ) :
    (upperSquareRoot z).im = Real.sqrt ((‖z‖ - z.re) / 2) := by simp [upperSquareRoot]

theorem upperSquareRoot_continuous : Continuous upperSquareRoot := by
  unfold upperSquareRoot
  fun_prop

theorem upperSquareRoot_sq {z : ℂ} (hz : 0 ≤ z.im) : (upperSquareRoot z) ^ 2 = z := by
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hp : 0 ≤ (‖z‖ + z.re) / 2 := by linarith [Complex.abs_re_le_norm z, neg_le_abs z.re]
  have hm : 0 ≤ (‖z‖ - z.re) / 2 := by linarith [Complex.re_le_norm z]
  have hA := Real.sq_sqrt hp
  have hB := Real.sq_sqrt hm
  have hAB : (2 * Real.sqrt ((‖z‖ + z.re) / 2) * Real.sqrt ((‖z‖ - z.re) / 2)) ^ 2 = z.im ^ 2 := by
    calc
      _ = 4 * (Real.sqrt ((‖z‖ + z.re) / 2) ^ 2 *
          Real.sqrt ((‖z‖ - z.re) / 2) ^ 2) := by ring
      _ = z.im ^ 2 := by rw [hA, hB]; nlinarith [hn]
  have hAB' : 2 * Real.sqrt ((‖z‖ + z.re) / 2) * Real.sqrt ((‖z‖ - z.re) / 2) = z.im := by
    exact (sq_eq_sq₀ (by positivity) hz).mp hAB
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re, upperSquareRoot_re, upperSquareRoot_im]
    nlinarith [hA, hB]
  · simp only [pow_two, Complex.mul_im, upperSquareRoot_re, upperSquareRoot_im]
    nlinarith [hAB']

theorem upperSquareRoot_re_pos {z : ℂ} (hz : 0 < z.im) : 0 < (upperSquareRoot z).re := by
  rw [upperSquareRoot_re, Real.sqrt_pos]
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsq : 0 < z.im ^ 2 := sq_pos_of_pos hz
  nlinarith [Complex.abs_re_le_norm z, neg_le_abs z.re, norm_nonneg z]

theorem upperSquareRoot_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (upperSquareRoot z).im := by
  rw [upperSquareRoot_im, Real.sqrt_pos]
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsq : 0 < z.im ^ 2 := sq_pos_of_pos hz
  nlinarith [Complex.re_le_norm z, norm_nonneg z]

/-- The branch whose imaginary part is positive throughout the upper
half-plane. -/
def semicircleRoot (z : ℂ) : ℂ := upperSquareRoot (z - 1) * upperSquareRoot (z + 1)

/-- The explicit candidate Cauchy transform of the semicircle profile. -/
def semicircleComplex (z : ℂ) : ℂ := semicircleRoot z - z

theorem semicircleRoot_continuous : Continuous semicircleRoot :=
  (upperSquareRoot_continuous.comp (continuous_id.sub continuous_const)).mul
    (upperSquareRoot_continuous.comp (continuous_id.add continuous_const))

theorem semicircleComplex_continuous : Continuous semicircleComplex :=
  semicircleRoot_continuous.sub continuous_id

theorem semicircleRoot_sq {z : ℂ} (hz : 0 ≤ z.im) : (semicircleRoot z) ^ 2 = z ^ 2 - 1 := by
  rw [semicircleRoot, mul_pow, upperSquareRoot_sq (by simpa using hz),
    upperSquareRoot_sq (by simpa using hz)]
  ring

theorem semicircleRoot_im_pos {z : ℂ} (hz : z ∈ upperHalfPlane) : 0 < (semicircleRoot z).im := by
  have h1 : 0 < (z - 1).im := by simpa [upperHalfPlane] using hz
  have h2 : 0 < (z + 1).im := by simpa [upperHalfPlane] using hz
  dsimp only [semicircleRoot]
  rw [Complex.mul_im]
  exact add_pos (mul_pos (upperSquareRoot_re_pos h1) (upperSquareRoot_im_pos h2))
    (mul_pos (upperSquareRoot_im_pos h1) (upperSquareRoot_re_pos h2))

@[simp] theorem upperSquareRoot_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) :
    upperSquareRoot (x : ℂ) = (Real.sqrt x : ℂ) := by
  unfold upperSquareRoot
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, abs_of_nonneg hx]
  rw [show (x + x) / 2 = x by ring, sub_self]
  simp

@[simp] theorem upperSquareRoot_ofReal_nonpos {x : ℝ} (hx : x ≤ 0) :
    upperSquareRoot (x : ℂ) = (Real.sqrt (-x) : ℂ) * Complex.I := by
  unfold upperSquareRoot
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, abs_of_nonpos hx]
  rw [neg_add_cancel, show (-x - x) / 2 = -x by ring]
  simp

/-- The square-root branch has the semicircle as its imaginary boundary value. -/
theorem semicircleRoot_ofReal_interior {x : ℝ} (hx : |x| ≤ 1) :
    semicircleRoot (x : ℂ) = (Real.sqrt (1 - x ^ 2) : ℂ) * Complex.I := by
  have hx1 : x - 1 ≤ 0 := by linarith [(abs_le.mp hx).2]
  have hx2 : 0 ≤ x + 1 := by linarith [(abs_le.mp hx).1]
  unfold semicircleRoot
  rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring,
    show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring,
    upperSquareRoot_ofReal_nonpos hx1, upperSquareRoot_ofReal_nonneg hx2]
  have hs : Real.sqrt (-(x - 1)) * Real.sqrt (x + 1) = Real.sqrt (1 - x ^ 2) := by
    rw [← Real.sqrt_mul (by linarith : 0 ≤ -(x - 1)), show -(x - 1) * (x + 1) = 1 - x ^ 2 by ring]
  calc
    _ = ((Real.sqrt (-(x - 1)) * Real.sqrt (x + 1) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    _ = _ := by rw [hs]

theorem semicircleComplex_boundary_im (x : ℝ) :
    (semicircleComplex (x : ℂ)).im = semicircleBarrier x := by
  by_cases hx : |x| ≤ 1
  · rw [semicircleComplex, Complex.sub_im, semicircleRoot_ofReal_interior hx]
    simp [semicircleBarrier_eq_sqrt]
  · have hbar : semicircleBarrier x = 0 := semicircleBarrier_zero_exterior x (le_of_not_ge hx)
    rw [hbar]
    rcases lt_or_gt_of_ne (show x ≠ 0 by intro h; simp [h] at hx) with hneg | hpos
    · have hx1 : x - 1 ≤ 0 := by linarith
      have hx2 : x + 1 ≤ 0 := by rw [abs_of_neg hneg] at hx; linarith
      simp only [semicircleComplex, semicircleRoot, Complex.sub_im, Complex.mul_im,
        Complex.ofReal_im, sub_zero]
      rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring,
        show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring,
        upperSquareRoot_ofReal_nonpos hx1, upperSquareRoot_ofReal_nonpos hx2]
      simp
    · have hx1 : 0 ≤ x - 1 := by rw [abs_of_pos hpos] at hx; linarith
      have hx2 : 0 ≤ x + 1 := by linarith
      simp only [semicircleComplex, semicircleRoot, Complex.sub_im, Complex.mul_im,
        Complex.ofReal_im, sub_zero]
      rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring,
        show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring,
        upperSquareRoot_ofReal_nonneg hx1, upperSquareRoot_ofReal_nonneg hx2]
      simp

theorem semicircleComplex_boundary_re {x : ℝ} (hx : |x| < 1) :
    (semicircleComplex (x : ℂ)).re = -x := by
  rw [semicircleComplex, Complex.sub_re, semicircleRoot_ofReal_interior hx.le]
  simp

/-- Holomorphy is obtained directly from the square identity and the
continuous branch's difference quotient. -/
theorem hasDerivAt_semicircleRoot {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasDerivAt semicircleRoot (z / semicircleRoot z) z := by
  have hzS : semicircleRoot z ≠ 0 := by
    intro h
    have := semicircleRoot_im_pos hz
    rw [h, Complex.zero_im] at this
    linarith
  have hden : semicircleRoot z + semicircleRoot z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im] at hi
    linarith [semicircleRoot_im_pos hz]
  have hlim := ((tendsto_id.add_const z).div
    ((semicircleRoot_continuous.tendsto z).add_const (semicircleRoot z)) hden).mono_left
      (show nhdsWithin z ({z}ᶜ) ≤ nhds z from nhdsWithin_le_nhds)
  have hval : (z + z) / (semicircleRoot z + semicircleRoot z) = z / semicircleRoot z := by
    field_simp
  rw [hval] at hlim
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply hlim.congr' ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds ((show IsOpen upperHalfPlane from isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz),
    self_mem_nhdsWithin] with w hw hwz
  have hne : w - z ≠ 0 := sub_ne_zero.mpr hwz
  have hS : semicircleRoot w + semicircleRoot z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im] at hi
    linarith [semicircleRoot_im_pos hw, semicircleRoot_im_pos hz]
  dsimp only [slope]
  simp only [smul_eq_mul, vsub_eq_sub, id_eq]
  rw [mul_comm, ← div_eq_mul_inv]
  apply (div_eq_div_iff hS hne).mpr
  simp only [Pi.div_apply, id_eq]
  linear_combination -(semicircleRoot_sq (show 0 ≤ w.im from (show 0 < w.im from hw).le)) +
    (semicircleRoot_sq (show 0 ≤ z.im from (show 0 < z.im from hz).le))

theorem semicircleComplex_differentiableOn : DifferentiableOn ℂ semicircleComplex upperHalfPlane :=
  fun z hz => ((hasDerivAt_semicircleRoot hz).sub (hasDerivAt_id z)).differentiableAt.differentiableWithinAt

/-- The explicit branch is holomorphic inside and continuous on the
closed upper half-plane, including both marked endpoints. -/
theorem semicircleComplex_diffContOnCl : DiffContOnCl ℂ semicircleComplex upperHalfPlane :=
  ⟨semicircleComplex_differentiableOn, semicircleComplex_continuous.continuousOn⟩

/-- The real part of the chosen root has the same sign as `Re z`. -/
theorem semicircleRoot_re_mul_re_nonneg {z : ℂ} (hz : z ∈ upperHalfPlane) :
    0 ≤ (semicircleRoot z).re * z.re := by
  have hsq := congrArg Complex.im (semicircleRoot_sq (show 0 ≤ z.im from (show 0 < z.im from hz).le))
  simp only [pow_two, Complex.mul_im, Complex.sub_im, Complex.one_im, sub_zero] at hsq
  have hmul : (semicircleRoot z).re * (semicircleRoot z).im = z.re * z.im := by nlinarith
  apply (mul_le_mul_iff_of_pos_right (semicircleRoot_im_pos hz)).mp
  simp only [zero_mul]
  calc
    _ = z.re ^ 2 * z.im := by linear_combination (z.re) * hmul
    _ ≥ 0 := mul_nonneg (sq_nonneg _) (show 0 ≤ z.im from (show 0 < z.im from hz).le)

private theorem semicircleRoot_dot_nonneg {z : ℂ} (hz : z ∈ upperHalfPlane) :
    0 ≤ (semicircleRoot z).re * z.re + (semicircleRoot z).im * z.im :=
  add_nonneg (semicircleRoot_re_mul_re_nonneg hz)
    (mul_nonneg (semicircleRoot_im_pos hz).le (show 0 ≤ z.im from (show 0 < z.im from hz).le))

theorem semicircleRoot_add_norm_ge {z : ℂ} (hz : z ∈ upperHalfPlane) :
    ‖z‖ ≤ ‖semicircleRoot z + z‖ := by
  have hd := semicircleRoot_dot_nonneg hz
  have hs : ‖z‖ ^ 2 ≤ ‖semicircleRoot z + z‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_add, Complex.normSq_apply,
      Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    nlinarith [sq_nonneg (semicircleRoot z).re, sq_nonneg (semicircleRoot z).im]
  nlinarith [norm_nonneg z, norm_nonneg (semicircleRoot z + z)]

private theorem semicircleRoot_sub_norm_le_add {z : ℂ} (hz : z ∈ upperHalfPlane) :
    ‖semicircleRoot z - z‖ ≤ ‖semicircleRoot z + z‖ := by
  have hd := semicircleRoot_dot_nonneg hz
  have hs : ‖semicircleRoot z - z‖ ^ 2 ≤ ‖semicircleRoot z + z‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub, Complex.normSq_apply,
      Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    nlinarith
  nlinarith [norm_nonneg (semicircleRoot z - z), norm_nonneg (semicircleRoot z + z)]

theorem semicircleComplex_mul_root_add {z : ℂ} (hz : 0 ≤ z.im) :
    semicircleComplex z * (semicircleRoot z + z) = -1 := by
  dsimp only [semicircleComplex]
  linear_combination semicircleRoot_sq hz

theorem semicircleComplex_eq_neg_inv {z : ℂ} (hz : 0 ≤ z.im) :
    semicircleComplex z = -1 / (semicircleRoot z + z) := by
  have hprod := semicircleComplex_mul_root_add hz
  have hden : semicircleRoot z + z ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    norm_num at hprod
  exact (eq_div_iff hden).mpr hprod

/-- The explicit semicircle Cauchy branch is bounded by one throughout
its actual holomorphic domain. -/
theorem semicircleComplex_norm_le_one {z : ℂ} (hz : z ∈ upperHalfPlane) :
    ‖semicircleComplex z‖ ≤ 1 := by
  have hprod : ‖semicircleComplex z‖ * ‖semicircleRoot z + z‖ = 1 := by
    rw [← norm_mul, semicircleComplex_mul_root_add (show 0 ≤ z.im from (show 0 < z.im from hz).le)]
    simp
  have hdiff : ‖semicircleComplex z‖ ≤ ‖semicircleRoot z + z‖ := semicircleRoot_sub_norm_le_add hz
  have hm := mul_le_mul_of_nonneg_left hdiff (norm_nonneg (semicircleComplex z))
  nlinarith [norm_nonneg (semicircleComplex z)]

/-- Quantitative decay of the explicit branch away from the origin. -/
theorem semicircleComplex_norm_le_inv_norm {z : ℂ} (hz : z ∈ upperHalfPlane) :
    ‖semicircleComplex z‖ ≤ ‖z‖⁻¹ := by
  have hz0 : z ≠ 0 := by intro h; have := (show 0 < z.im from hz); simp [h] at this
  have hprod : ‖semicircleComplex z‖ * ‖semicircleRoot z + z‖ = 1 := by
    rw [← norm_mul, semicircleComplex_mul_root_add (show 0 ≤ z.im from (show 0 < z.im from hz).le)]
    simp
  have hm := mul_le_mul_of_nonneg_left (semicircleRoot_add_norm_ge hz) (norm_nonneg (semicircleComplex z))
  have h : ‖semicircleComplex z‖ ≤ 1 / ‖z‖ := (le_div_iff₀ (norm_pos_iff.mpr hz0)).mpr (by linarith)
  simpa only [one_div] using h

/-- The branch tends to zero along the imaginary ray. -/
theorem semicircleComplex_tendsto_imaginary_ray :
    Tendsto (fun y : ℝ => semicircleComplex ((y : ℂ) * Complex.I)) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _) ?_ tendsto_inv_atTop_zero
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  have hyp : 0 < y := by linarith
  have hz : (y : ℂ) * Complex.I ∈ upperHalfPlane := by
    simpa only [upperHalfPlane, mem_setOf_eq, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] using hyp
  simpa only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_pos hyp] using semicircleComplex_norm_le_inv_norm hz

end Torsion.Spectral

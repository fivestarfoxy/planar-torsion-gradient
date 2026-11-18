module

public import Torsion.PhysicalCauchyHarmonicLift
public import Torsion.BoundaryLowerBound
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! # A harmonic barrier in the boundary rectangle -/

noncomputable section
open Set
open scoped ContDiff

namespace Torsion

def rectangleLambda (δ : ℝ) : ℝ := Real.pi / (2 * δ)

theorem rectangleLambda_pos {δ : ℝ} (hδ : 0 < δ) : 0 < rectangleLambda δ :=
  div_pos Real.pi_pos (mul_pos (by norm_num) hδ)

/-- Imaginary part of a scaled entire sine, with height slope bounded by `η`. -/
def rectangleBarrier (R δ η : ℝ) (z : Plane) : ℝ :=
  (((η * R / (rectangleLambda δ * Real.cosh (rectangleLambda δ)) : ℝ) : Plane) *
    Complex.sin (((rectangleLambda δ / R : ℝ) : Plane) * z)).im

theorem rectangleBarrier_formula (R δ η : ℝ) (z : Plane) :
    rectangleBarrier R δ η z = η * R / (rectangleLambda δ * Real.cosh (rectangleLambda δ)) *
      (Real.cos (rectangleLambda δ / R * z.re) * Real.sinh (rectangleLambda δ / R * z.im)) := by
  have him (w : Plane) : (Complex.sin w).im = Real.cos w.re * Real.sinh w.im := by
    rw [Complex.sin_eq]
    simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh, Complex.add_im, Complex.mul_im, Complex.mul_re]
  simp only [rectangleBarrier, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, him,
    Complex.mul_re, zero_mul, add_zero, sub_zero]

theorem rectangleBarrier_contDiff (R δ η : ℝ) : ContDiff ℝ ∞ (rectangleBarrier R δ η) := by
  rw [show rectangleBarrier R δ η = _ from funext (rectangleBarrier_formula R δ η)]
  exact contDiff_const.mul
    ((Real.contDiff_cos.comp (contDiff_const.mul Complex.reCLM.contDiff)).mul
      (Real.contDiff_sinh.comp (contDiff_const.mul Complex.imCLM.contDiff)))

theorem rectangleBarrier_laplacian (R δ η : ℝ) (z : Plane) :
    WeakHarmonicRegularity.planarLaplacian (rectangleBarrier R δ η) z = 0 := by
  let B (w : Plane) : Plane := ((η * R / (rectangleLambda δ * Real.cosh (rectangleLambda δ)) : ℝ) : Plane) *
    Complex.sin (((rectangleLambda δ / R : ℝ) : Plane) * w)
  have hB : AnalyticOnNhd ℂ B univ := by
    intro w _
    dsimp [B]
    fun_prop
  exact Spectral.planarLaplacian_im_eq_zero isOpen_univ hB.differentiableOn hB.deriv.differentiableOn
    (mem_univ z)

private theorem sinh_le_mul_cosh_of_le {v L : ℝ} (hv : 0 ≤ v) (hL : v ≤ L) :
    Real.sinh v ≤ v * Real.cosh L := by
  rcases hv.eq_or_lt with h | h
  · simp [← h]
  obtain ⟨c, hc, hm⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh h
    Real.continuous_sinh.continuousOn (fun x _ => Real.hasDerivAt_sinh x)
  rw [Real.sinh_zero, sub_zero, sub_zero, eq_div_iff h.ne'] at hm
  have hcL := Real.cosh_le_cosh.mpr (show |c| ≤ |L| by
    rw [abs_of_pos hc.1, abs_of_nonneg (hv.trans hL)]
    exact hc.2.le.trans hL)
  rw [← hm, mul_comm v]
  exact mul_le_mul_of_nonneg_right hcL hv

/-- The height estimate holds for every horizontal coordinate. -/
theorem rectangleBarrier_le_height {R δ η : ℝ} {z : Plane} (hR : 0 < R) (hδ : 0 < δ)
    (hη : 0 ≤ η) (hy0 : 0 ≤ z.im) (hyR : z.im ≤ R) :
    rectangleBarrier R δ η z ≤ η * z.im := by
  let L := rectangleLambda δ
  have hL : 0 < L := rectangleLambda_pos hδ
  have hv : 0 ≤ L / R * z.im := mul_nonneg (div_nonneg hL.le hR.le) hy0
  have hvL : L / R * z.im ≤ L := by
    calc
      _ ≤ L / R * R := mul_le_mul_of_nonneg_left hyR (div_nonneg hL.le hR.le)
      _ = L := div_mul_cancel₀ _ hR.ne'
  have hcosh := Real.cosh_pos L
  have hcoef : 0 ≤ η * R / (L * Real.cosh L) := by positivity
  rw [rectangleBarrier_formula]
  calc
    _ ≤ η * R / (L * Real.cosh L) * (L / R * z.im * Real.cosh L) := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      exact (mul_le_of_le_one_left (Real.sinh_nonneg_iff.mpr hv) (Real.cos_le_one _)).trans
        (sinh_le_mul_cosh_of_le hv hvL)
    _ = _ := by field_simp [hR.ne', hL.ne', hcosh.ne']

theorem rectangleBarrier_eq_zero_of_im_eq_zero (R δ η : ℝ) {z : Plane} (h : z.im = 0) :
    rectangleBarrier R δ η z = 0 := by simp [rectangleBarrier_formula, h]

theorem rectangleBarrier_eq_zero_of_side {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (η : ℝ)
    {z : Plane} (h : z.re = δ * R ∨ z.re = -(δ * R)) : rectangleBarrier R δ η z = 0 := by
  have heq : rectangleLambda δ / R * (δ * R) = Real.pi / 2 := by
    unfold rectangleLambda
    field_simp [hR.ne', hδ.ne']
  rcases h with h | h <;> simp [rectangleBarrier_formula, h, heq, mul_neg]

theorem rectangleBarrier_axis_formula (R δ η t : ℝ) :
    rectangleBarrier R δ η ((t : Plane) * Complex.I) =
      η * R / (rectangleLambda δ * Real.cosh (rectangleLambda δ)) *
        Real.sinh (rectangleLambda δ / R * t) := by
  rw [rectangleBarrier_formula]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, sub_zero, Complex.mul_im, mul_one, add_zero, Real.cos_zero, one_mul]

/-- Along the inward normal the barrier dominates a line of strictly positive slope
whenever `η > 0`. This form can be used directly in a comparison argument. -/
theorem rectangleBarrier_axis_lower {R δ η t : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hη : 0 ≤ η) (ht : 0 ≤ t) :
    η / Real.cosh (rectangleLambda δ) * t ≤ rectangleBarrier R δ η ((t : Plane) * Complex.I) := by
  let L := rectangleLambda δ
  have hL : 0 < L := rectangleLambda_pos hδ
  have hcosh := Real.cosh_pos L
  have hcoef : 0 ≤ η * R / (L * Real.cosh L) := by positivity
  rw [rectangleBarrier_axis_formula]
  calc
    _ = η * R / (L * Real.cosh L) * (L / R * t) := by
      change η / Real.cosh L * t = _
      field_simp [hR.ne', hL.ne', hcosh.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.self_le_sinh_iff.mpr (mul_nonneg (div_nonneg hL.le hR.le) ht)) hcoef

/-- Exact limit of the normal quotient at zero, in the paper's flux convention. -/
theorem rectangleBarrier_hasMarkedFlux {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (η : ℝ) :
    HasMarkedFlux (rectangleBarrier R δ η) (η / Real.cosh (rectangleLambda δ)) := by
  apply hasMarkedFlux_of_normal_derivative
    (rectangleBarrier_eq_zero_of_im_eq_zero R δ η Complex.zero_im)
  simp_rw [rectangleBarrier_axis_formula]
  let L := rectangleLambda δ
  let a := η * R / (L * Real.cosh L)
  let k := L / R
  have hd : HasDerivAt (fun t : ℝ => a * Real.sinh (k * t)) (a * k) 0 := by
    simpa using! (((Real.hasDerivAt_sinh (k * 0)).comp 0
      ((hasDerivAt_id (0 : ℝ)).const_mul k)).const_mul a)
  have heq : a * k = η / Real.cosh L := by
    dsimp only [a, k]
    have hL : L ≠ 0 := (rectangleLambda_pos hδ).ne'
    field_simp [hR.ne', hL, (Real.cosh_pos L).ne']
  exact heq ▸ hd

end Torsion

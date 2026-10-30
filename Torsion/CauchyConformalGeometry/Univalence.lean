module

public import Torsion.CauchyConformalGeometry.ImageSeparation
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.Convex

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Univalence from the concrete integral signs

The half-plane cone criterion below is proved by restricting to real
segments and applying the one-dimensional mean value theorem. It does not
invoke a Jordan or argument-principle hypothesis.
-/

noncomputable section
open Set

namespace Torsion.Spectral

/-- A holomorphic function with strictly negative imaginary derivative on
a real-convex set is injective there. The rotated secant has strictly
positive real derivative along each segment. -/
theorem injOn_of_im_deriv_neg {S : Set ℂ} (hS : Convex ℝ S) {f : ℂ → ℂ}
    (hd : ∀ z ∈ S, DifferentiableAt ℂ f z)
    (hi : ∀ z ∈ S, (deriv f z).im < 0) : InjOn f S := by
  intro z hz w hw heq
  by_contra hne
  have hdelta : w - z ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  let p : ℝ → ℂ := fun t => z + (t : ℂ) * (w - z)
  let g : ℂ → ℂ := fun t => Complex.I * ((f (z + t * (w - z)) - f z) / (w - z))
  let q : ℝ → ℝ := fun t => (g (t : ℂ)).re
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ S := by
    simpa only [p, Complex.real_smul] using hS.add_smul_sub_mem hz hw ht
  have hqd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt q (-(deriv f (p t)).im) t := by
    have hline : HasDerivAt (fun τ : ℂ => z + τ * (w - z)) (w - z) (t : ℂ) := by
      simpa only [Pi.add_apply, zero_add] using! (hasDerivAt_const (t : ℂ) z).add ((hasDerivAt_id (t : ℂ)).mul_const (w - z))
    have hf := ((hd _ (hp t ht)).hasDerivAt.comp (t : ℂ) hline).sub_const (f z)
    have hg := (hf.div_const (w - z)).const_mul Complex.I
    have hg' : HasDerivAt g (Complex.I * deriv f (p t)) (t : ℂ) := by
      convert! hg using 1
      dsimp [p]
      field_simp
    convert! hg'.real_of_complex using 1
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  have hqcont : ContinuousOn q (Icc (0 : ℝ) 1) :=
    fun t ht => (hqd t ht).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn q (Icc (0 : ℝ) 1) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 1) hqcont (by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
      rw [(hqd t ht').deriv]
      exact neg_pos.2 (hi _ (hp t ht')))
  have hlt := hmono (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) (by norm_num : (0 : ℝ) < 1)
  have hq0 : q 0 = 0 := by simp [q, g]
  have hq1 : q 1 = 0 := by simp [q, g, ← heq]
  rw [hq0, hq1] at hlt
  exact (lt_irrefl _ hlt)

theorem injOn_of_im_deriv_pos {S : Set ℂ} (hS : Convex ℝ S) {f : ℂ → ℂ}
    (hd : ∀ z ∈ S, DifferentiableAt ℂ f z)
    (hi : ∀ z ∈ S, 0 < (deriv f z).im) : InjOn f S := by
  have hn : InjOn (fun z => -f z) S := injOn_of_im_deriv_neg hS
    (fun z hz => (hd z hz).neg) (by
      intro z hz
      have hn : HasDerivAt (fun w => -f w) (-deriv f z) z := by
        simpa only [Pi.neg_apply] using! (hd z hz).hasDerivAt.neg
      rw [hn.deriv, Complex.neg_im]
      exact neg_neg_of_pos (hi z hz))
  intro z hz w hw heq
  exact hn hz hw (congrArg Neg.neg heq)

/-- The actual Cauchy map is injective on the right open quarter-plane. -/
theorem cauchy_injOn_right_quadrant {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    InjOn (cauchy φ) {z : ℂ | 0 < z.im ∧ 0 < z.re} := by
  apply injOn_of_im_deriv_neg
    ((convex_halfSpace_im_gt (0 : ℝ)).inter (convex_halfSpace_re_gt (0 : ℝ)))
  · intro z hz
    exact (hasDerivAt_cauchy hφ.continuousOn hz.1).differentiableAt
  · intro z hz
    exact cauchy_derivative_im_neg_of_re_pos hφ hodd hzero hpos hz.1 hz.2

theorem cauchy_injOn_left_quadrant {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    InjOn (cauchy φ) {z : ℂ | 0 < z.im ∧ z.re < 0} := by
  apply injOn_of_im_deriv_pos
    ((convex_halfSpace_im_gt (0 : ℝ)).inter (convex_halfSpace_re_lt (0 : ℝ)))
  · intro z hz
    exact (hasDerivAt_cauchy hφ.continuousOn hz.1).differentiableAt
  · intro z hz
    exact cauchy_derivative_im_pos_of_re_neg hφ hodd hzero hpos hz.1 hz.2

/-- The imaginary-axis height is strictly decreasing as the preimage moves
upward. The derivative is the negative real-axis value of F'. -/
theorem cauchy_axis_im_strictAntiOn {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    StrictAntiOn (fun y : ℝ => (cauchy φ ((y : ℂ) * Complex.I)).im) (Ioi 0) := by
  let q : ℝ → ℝ := fun y => (cauchy φ ((y : ℂ) * Complex.I)).im
  have hqd (y : ℝ) (hy : 0 < y) :
      HasDerivAt q (deriv (cauchy φ) ((y : ℂ) * Complex.I)).re y := by
    have hz : (y : ℂ) * Complex.I ∈ upperHalfPlane := by simpa [upperHalfPlane] using hy
    have hline : HasDerivAt (fun τ : ℂ => τ * Complex.I) Complex.I (y : ℂ) := by
      simpa using! (hasDerivAt_id (y : ℂ)).mul_const Complex.I
    have hf := (((hasDerivAt_cauchy hφ.continuousOn hz).differentiableAt.hasDerivAt).comp
      (y : ℂ) hline).const_mul (-Complex.I)
    have hder : HasDerivAt (fun τ : ℂ => -Complex.I * cauchy φ (τ * Complex.I))
        (deriv (cauchy φ) ((y : ℂ) * Complex.I)) (y : ℂ) := by
      convert! hf using 1
      calc
        deriv (cauchy φ) ((y : ℂ) * Complex.I) =
            (-Complex.I * Complex.I) * deriv (cauchy φ) ((y : ℂ) * Complex.I) := by simp
        _ = -Complex.I * (deriv (cauchy φ) ((y : ℂ) * Complex.I) * Complex.I) := by ring
    convert! hder.real_of_complex using 1
    funext t
    simp only [q, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, neg_zero, zero_mul, neg_mul, one_mul, zero_sub, neg_neg]
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro y hy
    exact (hqd y hy).continuousAt.continuousWithinAt
  · intro y hy
    have hy' : 0 < y := interior_subset hy
    rw [(hqd y hy').deriv]
    exact cauchy_derivative_re_neg_of_re_zero hφ hodd hzero hpos
      (by simpa [upperHalfPlane] using hy') (by simp)

/-- Injectivity on the separating imaginary axis follows from strict
monotonicity of the actual imaginary value. -/
theorem cauchy_injOn_axis {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    InjOn (cauchy φ) {z : ℂ | 0 < z.im ∧ z.re = 0} := by
  intro z hz w hw heq
  have hzeq : z = (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hz.2]
  have hweq : w = (w.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hw.2]
  have him : z.im = w.im := (cauchy_axis_im_strictAntiOn hφ hodd hzero hpos).injOn
    hz.1 hw.1 (by simpa only [← hzeq, ← hweq] using congrArg Complex.im heq)
  exact Complex.ext (hz.2.trans hw.2.symm) him

/-- The actual Cauchy transform is univalent on H. This proof is entirely
interior: paired integral signs separate the two half-images, and a
one-dimensional mean value argument proves injectivity within each half.
In particular no Jordan boundary or argument-principle result is assumed. -/
theorem cauchy_injOn_upperHalfPlane {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    InjOn (cauchy φ) upperHalfPlane := by
  intro z hz w hw heq
  have hre := congrArg Complex.re heq
  rcases lt_trichotomy z.re 0 with hzl | hzl | hzr
  · rcases lt_trichotomy w.re 0 with hwl | hwl | hwr
    · exact cauchy_injOn_left_quadrant hφ hodd hzero hpos ⟨hz, hzl⟩ ⟨hw, hwl⟩ heq
    · have h1 := cauchy_re_pos_of_re_neg hφ hodd hzero hpos hz hzl
      have h2 := cauchy_re_zero_of_re_zero hφ hodd hzero hw hwl
      linarith
    · have h1 := cauchy_re_pos_of_re_neg hφ hodd hzero hpos hz hzl
      have h2 := cauchy_re_neg_of_re_pos hφ hodd hzero hpos hw hwr
      linarith
  · rcases lt_trichotomy w.re 0 with hwl | hwl | hwr
    · have h1 := cauchy_re_zero_of_re_zero hφ hodd hzero hz hzl
      have h2 := cauchy_re_pos_of_re_neg hφ hodd hzero hpos hw hwl
      linarith
    · exact cauchy_injOn_axis hφ hodd hzero hpos ⟨hz, hzl⟩ ⟨hw, hwl⟩ heq
    · have h1 := cauchy_re_zero_of_re_zero hφ hodd hzero hz hzl
      have h2 := cauchy_re_neg_of_re_pos hφ hodd hzero hpos hw hwr
      linarith
  · rcases lt_trichotomy w.re 0 with hwl | hwl | hwr
    · have h1 := cauchy_re_neg_of_re_pos hφ hodd hzero hpos hz hzr
      have h2 := cauchy_re_pos_of_re_neg hφ hodd hzero hpos hw hwl
      linarith
    · have h1 := cauchy_re_neg_of_re_pos hφ hodd hzero hpos hz hzr
      have h2 := cauchy_re_zero_of_re_zero hφ hodd hzero hw hwl
      linarith
    · exact cauchy_injOn_right_quadrant hφ hodd hzero hpos ⟨hz, hzr⟩ ⟨hw, hwr⟩ heq

end Torsion.Spectral

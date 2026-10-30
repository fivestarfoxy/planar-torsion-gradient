module

public import Torsion.CauchyTransformExterior
public import Torsion.CauchyConformalGeometry.MarkedGeometry

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The exterior branches of the actual Cauchy boundary map

The positive square-kernel formula gives strict monotonicity on each closed
exterior ray. Together with the already embedded free arc and the strict
real-coordinate separation, this proves injectivity on the entire finite
real boundary.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The exterior tangent is the cast of a strictly positive real integral. -/
theorem cauchy_boundary_tangent_exterior_eq {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {x : ℝ} (hx : 1 < |x|) :
    cauchyDerivativeExtension φ (x : ℂ) =
      ((Real.pi⁻¹ * ∫ s in Icc (-1 : ℝ) 1, height φ s / (x - s) ^ 2 : ℝ) : ℂ) := by
  rw [cauchyDerivativeExtension_ofReal_exterior hφ hα0 hα1 hodd hzero hx]
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    integral_complex_ofReal, Complex.ofReal_mul, Complex.ofReal_inv]

/-- The genuine tangent points in the positive real direction on both
exterior real branches. -/
theorem cauchy_boundary_tangent_exterior_pos {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) {x : ℝ} (hx : 1 < |x|) :
    0 < (cauchyDerivativeExtension φ (x : ℂ)).re := by
  rw [cauchy_boundary_tangent_exterior_eq hφ hα0 hα1 hodd hzero hx, Complex.ofReal_re]
  apply mul_pos (inv_pos.2 Real.pi_pos)
  have hne : ∀ s ∈ Icc (-1 : ℝ) 1, x - s ≠ 0 := by
    intro s hs heq
    have hxs : x = s := sub_eq_zero.mp heq
    have hsabs := abs_le.2 hs
    rw [← hxs] at hsabs
    linarith
  have hk : ContinuousOn (fun s : ℝ => height φ s / (x - s) ^ 2) (Icc (-1 : ℝ) 1) :=
    (height_continuous (hφ.continuous hα0).continuousOn).continuousOn.div
      ((continuous_const.sub continuous_id).pow 2).continuousOn
      (fun s hs => pow_ne_zero 2 (hne s hs))
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (hk.intervalIntegrable_of_Icc (by norm_num))
    (fun s hs => div_pos (height_pos (hφ.continuous hα0).continuousOn hpos (abs_lt.2 hs))
      (sq_pos_of_ne_zero (hne s ⟨hs.1.le, hs.2.le⟩))) (by norm_num)

/-- Strict real monotonicity on the complete right exterior branch,
including its junction with the free arc. -/
theorem cauchy_boundary_re_strictMonoOn_Ici {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    StrictMonoOn (fun x : ℝ => (cauchyExtension φ (x : ℂ)).re) (Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (1 : ℝ))
    (Complex.continuous_re.comp
      (cauchy_boundary_contDiff_one hφ hα0 hα1 hodd hzero).continuous).continuousOn
  intro x hx
  have hx1 : 1 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero x)
  change 0 < deriv (fun x : ℝ => (cauchyExtension φ (x : ℂ)).re) x
  rw [show deriv (fun x : ℝ => (cauchyExtension φ (x : ℂ)).re) x =
      (cauchyDerivativeExtension φ (x : ℂ)).re from by
        simpa only [Function.comp_def, Complex.reCLM_apply] using hd.deriv]
  exact cauchy_boundary_tangent_exterior_pos hφ hα0 hα1 hodd hzero hpos
    (by rw [abs_of_pos (by linarith : 0 < x)]; exact hx1)

/-- Strict real monotonicity on the complete left exterior branch. -/
theorem cauchy_boundary_re_strictMonoOn_Iic {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    StrictMonoOn (fun x : ℝ => (cauchyExtension φ (x : ℂ)).re) (Iic (-1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic (-1 : ℝ))
    (Complex.continuous_re.comp
      (cauchy_boundary_contDiff_one hφ hα0 hα1 hodd hzero).continuous).continuousOn
  intro x hx
  have hx1 : x < -1 := by simpa only [interior_Iic, mem_Iio] using hx
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero x)
  change 0 < deriv (fun x : ℝ => (cauchyExtension φ (x : ℂ)).re) x
  rw [show deriv (fun x : ℝ => (cauchyExtension φ (x : ℂ)).re) x =
      (cauchyDerivativeExtension φ (x : ℂ)).re from by
        simpa only [Function.comp_def, Complex.reCLM_apply] using hd.deriv]
  exact cauchy_boundary_tangent_exterior_pos hφ hα0 hα1 hodd hzero hpos
    (by rw [abs_of_neg (by linarith : x < 0)]; linarith)

private theorem boundary_height_eq (φ : ℝ → ℝ) (x : ℝ) :
    (cauchyExtension φ (x : ℂ)).im = height φ x := by
  simp only [cauchyExtension_ofReal, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
    mul_zero, add_zero, zero_add]

/-- The actual boundary map is injective on the nonnegative half-line. -/
theorem cauchy_boundary_injOn_Ici_zero {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    InjOn (fun x : ℝ => cauchyExtension φ (x : ℂ)) (Ici 0) := by
  classical
  intro x hx y hy hxy
  simp only [mem_Ici, mem_Iic] at hx hy
  dsimp only at hxy
  have hi : height φ x = height φ y := by
    simpa only [boundary_height_eq] using congrArg Complex.im hxy
  by_cases hx1 : x < 1
  · have hy1 : y < 1 := by
      by_contra! hy1
      have hp := height_pos (x := x) (hφ.continuous hα0).continuousOn hpos
        (by rw [abs_of_nonneg hx]; exact hx1)
      rw [height_zero_of_one_le_abs φ (x := y) (by rw [abs_of_nonneg hy]; exact hy1)] at hi
      exact hp.ne' hi
    exact cauchy_boundary_injOn_interval hφ hα0 hα1 hodd hzero hpos
      ⟨by linarith, hx1.le⟩ ⟨by linarith, hy1.le⟩ hxy
  · have hx1 : 1 ≤ x := le_of_not_gt hx1
    have hy1 : 1 ≤ y := by
      by_contra! hy1
      have hp := height_pos (x := y) (hφ.continuous hα0).continuousOn hpos
        (by rw [abs_of_nonneg hy]; exact hy1)
      rw [height_zero_of_one_le_abs φ (x := x) (by rw [abs_of_nonneg hx]; exact hx1)] at hi
      exact hp.ne' hi.symm
    exact (cauchy_boundary_re_strictMonoOn_Ici hφ hα0 hα1 hodd hzero hpos).injOn hx1 hy1
      (congrArg Complex.re hxy)

/-- Reflection symmetry of the complete actual real boundary map. -/
theorem cauchy_boundary_neg_conj {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) (x : ℝ) :
    cauchyExtension φ ((-x : ℝ) : ℂ) = -star (cauchyExtension φ (x : ℂ)) := by
  apply Complex.ext
  · simpa only [Complex.neg_re, Complex.star_def, Complex.conj_re] using
      cauchy_boundary_re_odd hφ hα0 hα1 hodd hzero x
  · simp only [boundary_height_eq, Complex.neg_im, Complex.star_def, Complex.conj_im,
      neg_neg, height_even φ x]

/-- The actual boundary map is injective on the nonpositive half-line. -/
theorem cauchy_boundary_injOn_Iic_zero {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    InjOn (fun x : ℝ => cauchyExtension φ (x : ℂ)) (Iic 0) := by
  classical
  intro x hx y hy hxy
  simp only [mem_Ici, mem_Iic] at hx hy
  dsimp only at hxy
  have heq : cauchyExtension φ ((-x : ℝ) : ℂ) = cauchyExtension φ ((-y : ℝ) : ℂ) := by
    rw [cauchy_boundary_neg_conj hφ hα0 hα1 hodd hzero x,
      cauchy_boundary_neg_conj hφ hα0 hα1 hodd hzero y, hxy]
  have h := cauchy_boundary_injOn_Ici_zero hφ hα0 hα1 hodd hzero hpos
    (show -x ∈ Ici 0 from neg_nonneg.2 hx) (show -y ∈ Ici 0 from neg_nonneg.2 hy) heq
  exact neg_injective h

/-- The entire finite real boundary parametrization is injective. -/
theorem cauchy_boundary_injective {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    Function.Injective (fun x : ℝ => cauchyExtension φ (x : ℂ)) := by
  classical
  intro x y hxy
  dsimp only at hxy
  have hre := congrArg Complex.re hxy
  have h0 : (cauchyExtension φ (0 : ℂ)).re = 0 := by
    have h := cauchy_boundary_re_odd hφ hα0 hα1 hodd hzero 0
    simp only [neg_zero, Complex.ofReal_zero] at h
    linarith
  have hnonpos : ∀ t : ℝ, 0 ≤ t → (cauchyExtension φ (t : ℂ)).re ≤ 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht with ht | ht
    · simpa [← ht] using h0.le
    · exact (cauchy_boundary_re_neg_of_pos hφ hα0 hα1 hodd hzero hpos ht).le
  have hnonneg : ∀ t : ℝ, t ≤ 0 → 0 ≤ (cauchyExtension φ (t : ℂ)).re := by
    intro t ht
    rcases lt_or_eq_of_le ht with ht | ht
    · exact (cauchy_boundary_re_pos_of_neg hφ hα0 hα1 hodd hzero hpos ht).le
    · simpa [ht] using h0.ge
  rcases le_total 0 x with hx | hx
  · have hy : 0 ≤ y := by
      by_contra! hy
      have hp := cauchy_boundary_re_pos_of_neg hφ hα0 hα1 hodd hzero hpos hy
      linarith [hnonpos x hx]
    exact cauchy_boundary_injOn_Ici_zero hφ hα0 hα1 hodd hzero hpos hx hy hxy
  · have hy : y ≤ 0 := by
      by_contra! hy
      have hp := cauchy_boundary_re_neg_of_pos hφ hα0 hα1 hodd hzero hpos hy
      linarith [hnonneg x hx]
    exact cauchy_boundary_injOn_Iic_zero hφ hα0 hα1 hodd hzero hpos hx hy hxy

end Torsion.Spectral

module

public import Torsion.CauchyImageAreaBoundary

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual bottom-side area integral

The real part of the boundary field is supported in `[-1,1]`. Its integral
along every larger real segment is exactly `bM-aN`, with the actual moments
and the existing linear Hilbert boundary equation.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal Interval

namespace Torsion.Spectral

/-- The real bottom-side boundary integral has its exact moment value on
every segment containing the support. -/
theorem cauchyAreaField_bottom_re_integral {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {R : ℝ} (hR : 1 ≤ R) :
    (∫ x : ℝ in -R..R, (cauchyAreaField φ (x : Plane)).re) =
      b * mass φ - a * squareMass φ := by
  let f : ℝ → ℝ := fun x => height φ x * (b - a * height φ x)
  have hf (x : ℝ) : (cauchyAreaField φ (x : Plane)).re = f x :=
    cauchyAreaField_ofReal_re hφ hα0 hzero hlinear x
  have hsupport : Function.support f ⊆ Ioc (-R) R := by
    intro x hx
    have hlt : |x| < 1 := by
      by_contra h
      have hz : height φ x = 0 := height_zero_of_one_le_abs φ (le_of_not_gt h)
      exact hx (by simp [f, hz])
    have habs := abs_lt.mp hlt
    constructor <;> linarith [habs.1, habs.2]
  have hY : Continuous (height φ) := height_continuous (hφ.continuous hα0).continuousOn
  have hYi : Integrable (height φ) := height_integrable (hφ.continuous hα0).continuousOn
  have hYsq : Integrable (fun x => (height φ x) ^ 2) :=
    (hY.fun_pow 2).integrable_of_hasCompactSupport ((height_hasCompactSupport φ).comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
  have hzout (x : ℝ) (hx : x ∉ Icc (-1 : ℝ) 1) : height φ x = 0 := by
    apply height_zero_of_one_le_abs φ
    apply (lt_of_not_ge _).le
    intro habs
    exact hx (abs_le.mp habs)
  have hM : (∫ x : ℝ, height φ x) = mass φ := by
    symm
    change (∫ x in Icc (-1 : ℝ) 1, height φ x) = _
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzout
  have hN : (∫ x : ℝ, (height φ x) ^ 2) = squareMass φ := by
    symm
    change (∫ x in Icc (-1 : ℝ) 1, (height φ x) ^ 2) = _
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [hzout x hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  calc
    _ = ∫ x : ℝ in -R..R, f x := by simp only [hf]
    _ = ∫ x : ℝ, f x := intervalIntegral.integral_eq_integral_of_support_subset hsupport
    _ = ∫ x : ℝ, b * height φ x - a * (height φ x) ^ 2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [f]; ring
    _ = b * mass φ - a * squareMass φ := by
      rw [integral_sub (hYi.const_mul b) (hYsq.const_mul a),
        integral_const_mul, integral_const_mul, hM, hN]

/-- Taking the real component commutes with the genuine continuous
complex bottom-side field integral. -/
theorem cauchyAreaField_bottom_integral_re {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {R : ℝ} (hR : 1 ≤ R) :
    (∫ x : ℝ in -R..R, cauchyAreaField φ (x : Plane)).re =
      b * mass φ - a * squareMass φ := by
  have hc : Continuous (fun x : ℝ => cauchyAreaField φ (x : Plane)) :=
    (cauchyAreaField_continuousOn hφ hα0 hα1 hodd hzero).comp_continuous
      Complex.continuous_ofReal ofReal_mem_closure_upperHalfPlane
  have hi : IntervalIntegrable (fun x : ℝ => cauchyAreaField φ (x : Plane))
      volume (-R) R := hc.intervalIntegrable (-R) R
  have heq := Complex.reCLM.intervalIntegral_comp_comm hi
  calc
    _ = ∫ x : ℝ in -R..R, (cauchyAreaField φ (x : Plane)).re := heq.symm
    _ = _ := cauchyAreaField_bottom_re_integral hφ hα0 hzero hlinear hR

end Torsion.Spectral

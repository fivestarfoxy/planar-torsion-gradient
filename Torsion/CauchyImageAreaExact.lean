module

public import Torsion.CauchyImageAreaBottom
public import Torsion.CauchyImageAreaDecay
public import Torsion.CauchyImageAreaExhaustion

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Exact Euclidean area of the actual Cauchy image

The Jacobian change of variables, Green's rectangle theorem, actual outer
boundary estimates and rectangle exhaustion identify Lebesgue area with
the explicit height moments. The area is not defined by a signed boundary
integral, and no geometric-area identity is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace Torsion.Spectral

/-- The actual Euclidean area is the exact moment expression in (16). -/
theorem area_cauchyImage_eq_moments {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    (volume (cauchyImage φ)).toReal = a * squareMass φ - b * mass φ := by
  let R : ℕ → ℝ := fun n => (n : ℝ) + 2
  let T : ℕ → ℂ := fun n => ∫ x : ℝ in -(R n)..R n,
    cauchyAreaField φ ((x : Plane) + ((R n : ℝ) : Plane) * Complex.I)
  let P : ℕ → ℂ := fun n => ∫ y : ℝ in (0 : ℝ)..R n,
    cauchyAreaField φ (((R n : ℝ) : Plane) + (y : Plane) * Complex.I)
  let L : ℕ → ℂ := fun n => ∫ y : ℝ in (0 : ℝ)..R n,
    cauchyAreaField φ ((-(R n : ℝ) : Plane) + (y : Plane) * Complex.I)
  let E : ℕ → ℝ := fun n => ∫ x : ℝ in -(R n)..R n, ∫ y : ℝ in (0 : ℝ)..R n,
    ‖cauchyDerivativeExtension φ ((x : Plane) + (y : Plane) * Complex.I)‖ ^ 2
  have hT : Tendsto T atTop (𝓝 0) := cauchyAreaField_top_integral_tendsto_zero
    (hφ.continuous hα0) hodd hzero
  have hP : Tendsto P atTop (𝓝 0) := by
    simpa only [one_mul] using cauchyAreaField_side_integral_tendsto_zero
      (hφ.continuous hα0) hodd hzero (σ := 1) (by norm_num)
  have hL : Tendsto L atTop (𝓝 0) := by
    simpa only [neg_one_mul, Complex.ofReal_neg] using cauchyAreaField_side_integral_tendsto_zero
      (hφ.continuous hα0) hodd hzero (σ := -1) (by norm_num)
  have hE : Tendsto E atTop (𝓝 ((volume (cauchyImage φ)).toReal)) :=
    cauchy_rectangle_energy_tendsto_area (hφ.continuous hα0) hodd hzero hpos
  have hsum : Tendsto (fun n => b * mass φ - a * squareMass φ - (T n).re +
      (Complex.I * P n).re - (Complex.I * L n).re) atTop
      (𝓝 (b * mass φ - a * squareMass φ)) := by
    have h0 : Tendsto (fun _ : ℕ => b * mass φ - a * squareMass φ) atTop
        (𝓝 (b * mass φ - a * squareMass φ)) := tendsto_const_nhds
    have h := ((h0.sub ((Complex.continuous_re.tendsto 0).comp hT)).add
      ((Complex.continuous_re.tendsto (Complex.I * 0)).comp (hP.const_mul Complex.I))).sub
      ((Complex.continuous_re.tendsto (Complex.I * 0)).comp (hL.const_mul Complex.I))
    simpa only [mul_zero, Complex.zero_re, sub_zero, add_zero, Function.comp_apply] using! h
  have heq (n : ℕ) : b * mass φ - a * squareMass φ - (T n).re +
      (Complex.I * P n).re - (Complex.I * L n).re = -E n := by
    have hn : 1 ≤ R n := by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have h := congrArg Complex.re
      (cauchyAreaField_rectangle_identity hφ hα0 hα1 hodd hzero (le_trans (by norm_num) hn))
    simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re] at h
    rw [cauchyAreaField_bottom_integral_re hφ hα0 hα1 hodd hzero hlinear hn] at h
    exact h
  have he := tendsto_nhds_unique (hsum.congr' (Eventually.of_forall heq)) hE.neg
  linarith

/-- The holomorphic moment identity reduces actual Euclidean area to `bM`. -/
theorem area_cauchyImage_eq_coefficient_mass {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    (volume (cauchyImage φ)).toReal = b * mass φ := by
  rw [area_cauchyImage_eq_moments hφ hα0 hα1 hodd hzero hpos hlinear]
  have hm := moment_identity_of_holder_boundary_equation ha hφ hα0 hα1 hodd hzero hlinear
  linarith

/-- Equation (17), for actual complex-plane Lebesgue area. -/
theorem area_cauchyImage_eq_half_squareMass {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    (volume (cauchyImage φ)).toReal = a * squareMass φ / 2 := by
  rw [area_cauchyImage_eq_coefficient_mass ha hφ hα0 hα1 hodd hzero hpos hlinear]
  have hm := moment_identity_of_holder_boundary_equation ha hφ hα0 hα1 hodd hzero hlinear
  linarith

/-- The equivalent nonnegative-measure formulation of the exact area law. -/
theorem volume_cauchyImage_eq_half_squareMass {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    volume (cauchyImage φ) = ENNReal.ofReal (a * squareMass φ / 2) := by
  rw [← area_cauchyImage_eq_half_squareMass ha hφ hα0 hα1 hodd hzero hpos hlinear]
  exact (ENNReal.ofReal_toReal
    (volume_cauchy_image_lt_top (hφ.continuous hα0) hodd hzero).ne).symm

end Torsion.Spectral

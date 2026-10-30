module

public import Torsion.CauchyShapeHadamard

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The oriented physical boundary density in the Hadamard formula -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral

/-- The constructed datum is the torsion boundary flux times the genuine
outward normal speed. -/
theorem shapeBoundaryData_eq_normalSpeed (a : ℝ) (φ : ℝ → ℝ)
    (V : Plane → Plane) (t : ℝ)
    (hne : cauchyDerivativeExtension φ (t : Plane) ≠ 0) :
    shapeBoundaryData a φ V t =
      (‖cauchyDerivativeExtension φ (t : Plane)‖ / (2 * a)) *
        inner (𝕜 := ℝ) (V (cauchyExtension φ (t : Plane))) (cauchyOutwardNormal φ t) := by
  have hn : ‖cauchyDerivativeExtension φ (t : Plane)‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hdiv : Complex.I * cauchyDerivativeExtension φ (t : Plane) / ((2 * a : ℝ) : Plane) =
      (2 * a)⁻¹ • (Complex.I * cauchyDerivativeExtension φ (t : Plane)) := by
    simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  simp only [shapeBoundaryData, hdiv, cauchyOutwardNormal, cauchyInwardNormal,
    inner_neg_right, real_inner_smul_right]
  rw [div_eq_mul_inv]
  generalize hX : inner (𝕜 := ℝ) (V (cauchyExtension φ (t : Plane)))
    (Complex.I * cauchyDerivativeExtension φ (t : Plane)) = X
  generalize hN : ‖cauchyDerivativeExtension φ (t : Plane)‖ = N at hn ⊢
  have hcancel : N * N⁻¹ = 1 := mul_inv_cancel₀ hn
  linear_combination ((2 * a)⁻¹ * X) * hcancel

/-- With the proved mass-one Green normalization, the conformal boundary
datum divided by M is exactly `q k (V·ν) ds/dt`. -/
theorem shapeBoundaryData_div_mass_eq_boundary_density
    (a : ℝ) (φ : ℝ → ℝ) (V : Plane → Plane) (t : ℝ)
    (hne : cauchyDerivativeExtension φ (t : Plane) ≠ 0) :
    shapeBoundaryData a φ V t / mass φ =
      (‖cauchyDerivativeExtension φ (t : Plane)‖ / (2 * a)) *
        (1 / (mass φ * ‖cauchyDerivativeExtension φ (t : Plane)‖)) *
          inner (𝕜 := ℝ) (V (cauchyExtension φ (t : Plane))) (cauchyOutwardNormal φ t) *
            ‖cauchyDerivativeExtension φ (t : Plane)‖ := by
  rw [shapeBoundaryData_eq_normalSpeed a φ V t hne]
  have hn : ‖cauchyDerivativeExtension φ (t : Plane)‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  generalize hX : inner (𝕜 := ℝ) (V (cauchyExtension φ (t : Plane)))
    (cauchyOutwardNormal φ t) = X
  generalize hN : ‖cauchyDerivativeExtension φ (t : Plane)‖ = N at hn ⊢
  simp only [div_eq_mul_inv, one_div, mul_inv]
  have hcancel : N * N⁻¹ = 1 := mul_inv_cancel₀ hn
  linear_combination -(N * (2 * a)⁻¹ * X * (mass φ)⁻¹) * hcancel

/-- The localized physical Hadamard formula in the actual free-boundary
parameter: `q k (V·ν) ds`, with the genuine outward normal, torsion and
Poisson normal traces, and actual arclength speed `|F'|`. -/
theorem torsionFlux_cauchy_boundary_hadamard
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVU : tsupport V ⊆ upperHalfPlane) :
    HasDerivAt (fun t : ℝ => torsionFlux (Shape.deformation V t '' cauchyImage φ))
      (∫ s in Icc (-1 : ℝ) 1,
        (‖cauchyDerivativeExtension φ (s : Plane)‖ / (2 * a)) *
          (1 / (mass φ * ‖cauchyDerivativeExtension φ (s : Plane)‖)) *
            inner (𝕜 := ℝ) (V (cauchyExtension φ (s : Plane))) (cauchyOutwardNormal φ s) *
              ‖cauchyDerivativeExtension φ (s : Plane)‖) 0 := by
  have h := torsionFlux_cauchy_deformation_hasDerivAt hEig ha hφ hα0 hα1 hodd hzero hpos
    hlinear hV hVc hVU
  have heq : (∫ s in Icc (-1 : ℝ) 1,
      (‖cauchyDerivativeExtension φ (s : Plane)‖ / (2 * a)) *
        (1 / (mass φ * ‖cauchyDerivativeExtension φ (s : Plane)‖)) *
          inner (𝕜 := ℝ) (V (cauchyExtension φ (s : Plane))) (cauchyOutwardNormal φ s) *
            ‖cauchyDerivativeExtension φ (s : Plane)‖) =
      (∫ s in Icc (-1 : ℝ) 1, shapeBoundaryData a φ V s) / mass φ := by
    rw [← integral_div]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact (shapeBoundaryData_div_mass_eq_boundary_density a φ V s
      (cauchyDerivativeExtension_ne_zero_on_interval ha hφ hα0 hα1 hodd hzero hpos hlinear hs)).symm
  rw [heq]
  exact h

end Torsion.Spectral

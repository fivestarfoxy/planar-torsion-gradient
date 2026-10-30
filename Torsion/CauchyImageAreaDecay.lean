module

public import Torsion.CauchyImageAreaBoundary

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Vanishing outer sides in the half-plane area calculation

These are estimates for the actual continuous Cauchy area field. Boundedness
of `F` and the proved inverse-square decay of `F′` give vanishing top and
side integrals along the expanding rectangles used in Green's theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal Interval

namespace Torsion.Spectral

/-- A uniform outer bound on the actual area field, following from the
actual integral formula for `F′` and the proved boundedness of `F`. -/
theorem cauchyAreaField_exists_decay_bound {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (R : ℝ), 1 < R → ∀ z ∈ upperHalfPlane, R ≤ ‖z‖ →
      ‖cauchyAreaField φ z‖ ≤ K / (R - 1) ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := cauchy_exists_norm_bound hφ hodd hzero
  let J : ℝ := ∫ s in Icc (-1 : ℝ) 1, ‖(height φ s : ℂ)‖
  let P : ℝ := ‖(Real.pi : ℂ)⁻¹‖
  have hJ : 0 ≤ J := integral_nonneg fun _ => norm_nonneg _
  have hP : 0 ≤ P := norm_nonneg _
  refine ⟨B * (P * J), mul_nonneg hB0 (mul_nonneg hP hJ), ?_⟩
  intro R hR z hz hRz
  have hn : 1 < ‖z‖ := hR.trans_le hRz
  have hD : ‖deriv (cauchy φ) z‖ ≤ (P * J) / (R - 1) ^ 2 := by
    rw [deriv_cauchy_eq hφ.continuousOn hz, norm_mul]
    calc
      _ ≤ P * (J / (‖z‖ - 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_cauchy_square_integral_le
          (Complex.continuous_ofReal.comp (height_continuous hφ.continuousOn)).continuousOn hn) hP
      _ ≤ P * (J / (R - 1) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hP
        exact div_le_div_of_nonneg_left hJ (sq_pos_of_pos (by linarith))
          (pow_le_pow_left₀ (by linarith) (by linarith) 2)
      _ = (P * J) / (R - 1) ^ 2 := by ring
  rw [cauchyAreaField, cauchyExtension_eq hφ.continuousOn hz,
    cauchyDerivativeExtension_eq hφ hodd hzero hz, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  calc
    _ ≤ B * ((P * J) / (R - 1) ^ 2) :=
      mul_le_mul ((Complex.abs_im_le_norm (cauchy φ z)).trans (hB z hz)) hD
        (norm_nonneg _) hB0
    _ = B * (P * J) / (R - 1) ^ 2 := by ring

/-- On an upper rectangle with side length `R`, the actual top integral
has a bound tending to zero as the rectangle expands. -/
theorem cauchyAreaField_outer_integral_bounds {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 < R →
      ‖∫ x : ℝ in -R..R,
        cauchyAreaField φ ((x : Plane) + (R : Plane) * Complex.I)‖ ≤
          2 * R * K / (R - 1) ^ 2 ∧
      ∀ σ : ℝ, |σ| = 1 →
        ‖∫ y : ℝ in (0 : ℝ)..R,
          cauchyAreaField φ (((σ * R : ℝ) : Plane) + (y : Plane) * Complex.I)‖ ≤
            R * K / (R - 1) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := cauchyAreaField_exists_decay_bound hφ hodd hzero
  refine ⟨K, hK0, ?_⟩
  intro R hR
  have hR0 : 0 < R := by linarith
  constructor
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -R) (b := R) (C := K / (R - 1) ^ 2)
      (f := fun x => cauchyAreaField φ ((x : Plane) + (R : Plane) * Complex.I))
      (fun x _ => hK R hR _ (by simpa [upperHalfPlane] using hR0)
        (by simpa using Complex.im_le_norm ((x : Plane) + (R : Plane) * Complex.I)))
    convert h using 1
    rw [show R - -R = 2 * R by ring, abs_of_pos (by linarith : (0 : ℝ) < 2 * R)]
    ring
  · intro σ hσ
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := R) (C := K / (R - 1) ^ 2)
      (f := fun y => cauchyAreaField φ (((σ * R : ℝ) : Plane) + (y : Plane) * Complex.I))
      (fun y hy => hK R hR _ (by
          have hy0 : 0 < y := by simpa only [min_eq_left hR0.le] using hy.1
          simpa [upperHalfPlane] using hy0)
        (by simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
          sub_self, add_zero, abs_mul, hσ, one_mul, abs_of_pos hR0]
          using Complex.abs_re_le_norm (((σ * R : ℝ) : Plane) + (y : Plane) * Complex.I)))
    convert h using 1
    rw [sub_zero, abs_of_pos hR0]
    ring

private theorem rectangle_decay_ratio_bound {R K : ℝ} (hR : 2 ≤ R) (hK : 0 ≤ K) :
    2 * R * K / (R - 1) ^ 2 ≤ 4 * K / (R - 1) := by
  have hden : 0 < R - 1 := by linarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hden) hden).2
  nlinarith [mul_nonneg hK (sub_nonneg.2 hR)]

/-- The actual top-side contribution in the area identity vanishes on
rectangles with `R = n+2`. -/
theorem cauchyAreaField_top_integral_tendsto_zero {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in -((n : ℝ) + 2)..((n : ℝ) + 2),
      cauchyAreaField φ ((x : Plane) + (((n : ℝ) + 2 : ℝ) : Plane) * Complex.I))
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := cauchyAreaField_outer_integral_bounds hφ hodd hzero
  have hlim : Tendsto (fun n : ℕ => 4 * K / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 * K)
  apply squeeze_zero_norm' _ hlim
  apply Eventually.of_forall
  intro n
  have hn : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hb := (hbound ((n : ℝ) + 2) (by linarith [Nat.cast_nonneg (α := ℝ) n])).1
  have hh := hb.trans (rectangle_decay_ratio_bound hn hK)
  convert hh using 1
  ring

/-- Each actual vertical-side contribution in the area identity vanishes
on the same expanding rectangles. -/
theorem cauchyAreaField_side_integral_tendsto_zero {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) {σ : ℝ} (hσ : |σ| = 1) :
    Tendsto (fun n : ℕ => ∫ y : ℝ in (0 : ℝ)..((n : ℝ) + 2),
      cauchyAreaField φ (((σ * ((n : ℝ) + 2) : ℝ) : Plane) + (y : Plane) * Complex.I))
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := cauchyAreaField_outer_integral_bounds hφ hodd hzero
  have hlim : Tendsto (fun n : ℕ => 4 * K / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 * K)
  apply squeeze_zero_norm' _ hlim
  apply Eventually.of_forall
  intro n
  have hn : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hb := (hbound ((n : ℝ) + 2) (by linarith [Nat.cast_nonneg (α := ℝ) n])).2 σ hσ
  have hfirst : ((n : ℝ) + 2) * K / ((n : ℝ) + 2 - 1) ^ 2 ≤
      2 * ((n : ℝ) + 2) * K / ((n : ℝ) + 2 - 1) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith [mul_nonneg hK (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2)]
  have hh := hb.trans (hfirst.trans (rectangle_decay_ratio_bound hn hK))
  convert hh using 1
  ring

end Torsion.Spectral

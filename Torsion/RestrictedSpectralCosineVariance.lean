import Mathlib.Analysis.SpecialFunctions.Integrals

/-! Exact elementary cosine variance on the restricted interval. -/
noncomputable section
open Set MeasureTheory

namespace Torsion.Spectral

/-- The squared norm of the cosine after projection away from constants. -/
theorem integral_cosine_variance {ξ : ℝ} (hξ : ξ ≠ 0) :
    (∫ x in Icc (-1 : ℝ) 1, (Real.cos (x * ξ) - Real.sin ξ / ξ) ^ 2) =
      1 + (Real.sin ξ / ξ) * Real.cos ξ - 2 * (Real.sin ξ / ξ) ^ 2 := by
  let u : ℝ := Real.sin ξ / ξ
  have hcos : (∫ x in Icc (-1 : ℝ) 1, Real.cos (x * ξ)) = 2 * u := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral.integral_comp_mul_right Real.cos hξ, integral_cos]
    simp only [one_mul, neg_one_mul, Real.sin_neg, smul_eq_mul, sub_neg_eq_add]
    dsimp only [u]
    field_simp
    ring
  have hcos2 : (∫ x in Icc (-1 : ℝ) 1, Real.cos (x * ξ) ^ 2) =
      1 + u * Real.cos ξ := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral.integral_comp_mul_right (fun x => Real.cos x ^ 2) hξ, integral_cos_sq]
    simp only [one_mul, neg_one_mul, Real.cos_neg, Real.sin_neg, smul_eq_mul]
    dsimp only [u]
    field_simp
    ring
  have hci : IntegrableOn (fun x : ℝ => Real.cos (x * ξ) ^ 2) (Icc (-1 : ℝ) 1) :=
    ((Real.continuous_cos.comp (continuous_id.mul continuous_const)).pow 2).integrableOn_Icc
  have hli : IntegrableOn (fun x : ℝ => 2 * u * Real.cos (x * ξ)) (Icc (-1 : ℝ) 1) :=
    (continuous_const.mul (Real.continuous_cos.comp (continuous_id.mul continuous_const))).integrableOn_Icc
  have hki : IntegrableOn (fun _ : ℝ => u ^ 2) (Icc (-1 : ℝ) 1) :=
    continuous_const.integrableOn_Icc
  calc
    _ = ∫ x in Icc (-1 : ℝ) 1, (Real.cos (x * ξ) ^ 2 -
        2 * u * Real.cos (x * ξ)) + u ^ 2 := by
      congr 1
      funext x
      dsimp only [u]
      ring
    _ = _ := by
      have ha : (∫ x in Icc (-1 : ℝ) 1, Real.cos (x * ξ) ^ 2 -
          2 * u * Real.cos (x * ξ) + u ^ 2) =
          (∫ x in Icc (-1 : ℝ) 1, Real.cos (x * ξ) ^ 2 - 2 * u * Real.cos (x * ξ)) +
          ∫ x in Icc (-1 : ℝ) 1, u ^ 2 := integral_add (hci.sub hli) hki
      have hb : (∫ x in Icc (-1 : ℝ) 1, Real.cos (x * ξ) ^ 2 -
          2 * u * Real.cos (x * ξ)) =
          (∫ x in Icc (-1 : ℝ) 1, Real.cos (x * ξ) ^ 2) -
          ∫ x in Icc (-1 : ℝ) 1, 2 * u * Real.cos (x * ξ) := integral_sub hci hli
      rw [ha, hb, integral_const_mul, hcos, hcos2, setIntegral_const,
        Real.volume_real_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      simp only [smul_eq_mul]
      dsimp only [u]
      ring

/-- A uniform rational bound for the projected cosine squared norm. -/
theorem integral_cosine_variance_le {ξ : ℝ} (hξ : ξ ≠ 0) :
    (∫ x in Icc (-1 : ℝ) 1, (Real.cos (x * ξ) - Real.sin ξ / ξ) ^ 2) ≤ (9 / 8 : ℝ) := by
  rw [integral_cosine_variance hξ]
  nlinarith [sq_nonneg (4 * (Real.sin ξ / ξ) - Real.cos ξ),
    Real.sin_sq_add_cos_sq ξ, sq_nonneg (Real.sin ξ)]

end Torsion.Spectral

module

public import Torsion.Proof.PaperNormalizedFlatSide
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! # A quantitative flat patch at the maximizing midpoint -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory

namespace Torsion.Spectral

/-- Concavity bounds the remaining integrated height by the area of a
horizontally and vertically contracted copy of the whole profile. -/
theorem secondHeight_quadratic_lower_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) ^ 2 * height secondEigenfunction 0 ≤ height secondEigenfunction t := by
  have hheight (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      height secondEigenfunction x = ∫ s in x..1, secondEigenfunction s := by
    rw [height_eq_clamped_integral, abs_of_nonneg hx.1, min_eq_left hx.2]
  have hzero : secondEigenfunction 1 = 0 := secondEigenfunction_zero_exterior 1 (by norm_num)
  have hnonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hmono : (1 - t) * (∫ x in (0 : ℝ)..1, secondEigenfunction x) ≤
      ∫ x in (0 : ℝ)..1, secondEigenfunction ((1 - t) * x + t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.mul secondEigenfunction_continuous).intervalIntegrable _ _)
      ((secondEigenfunction_continuous.comp
        ((continuous_const.mul continuous_id).add continuous_const)).intervalIntegrable _ _)
    intro x hx
    change (1 - t) * secondEigenfunction x ≤ secondEigenfunction ((1 - t) * x + t)
    simpa only [smul_eq_mul, mul_one, hzero, mul_zero, add_zero] using
      secondEigenfunction_concaveOn.2 hx (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
        hnonneg ht.1 (by ring : 1 - t + t = 1)
  have hsub := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
    secondEigenfunction (1 - t) t
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] at hsub
  rw [hheight t ht, hheight 0 (by norm_num), ← hsub, pow_two, mul_assoc]
  exact mul_le_mul_of_nonneg_left hmono hnonneg

private theorem secondMass_eq_twice_integral :
    secondMoments.M = 2 * ∫ t in (0 : ℝ)..1, height secondEigenfunction t := by
  rw [secondMoments_M, mass, pair_integrable_interval
    (height_integrableOn secondEigenfunction_continuous.continuousOn),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [height_even secondEigenfunction t, two_mul]

/-- Integrate the quadratic height lower bound, using the symmetry of the profile. -/
theorem secondHeight_zero_le_three_halves_mass :
    height secondEigenfunction 0 ≤ 3 / 2 * secondMoments.M := by
  have hc := height_continuous secondEigenfunction_continuous.continuousOn
  have hm : (∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * height secondEigenfunction 0) ≤
      ∫ t in (0 : ℝ)..1, height secondEigenfunction t :=
    intervalIntegral.integral_mono_on zero_le_one
      ((((continuous_const.sub continuous_id).pow 2).mul continuous_const).intervalIntegrable _ _)
      (hc.intervalIntegrable _ _) (fun _ ht => secondHeight_quadratic_lower_bound ht)
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 2) 1] at hm
  norm_num [integral_pow] at hm
  rw [secondMass_eq_twice_integral]
  linarith

/-- The even part of the endpoint Cauchy kernel dominates the constant weight. -/
theorem secondMass_div_pi_le_flatHalfWidth :
    secondMoments.M / Real.pi ≤ secondUnscaledFlatHalfWidth := by
  let Y := height secondEigenfunction
  have hc : Continuous Y := height_continuous secondEigenfunction_continuous.continuousOn
  have hnn : ∀ t, 0 ≤ Y t := height_nonneg (nonneg_on_unitInterval_of_odd_positive
    secondEigenfunction_odd secondEigenfunction_zero_exterior secondEigenfunction_pos)
  have hquot : IntegrableOn (fun t : ℝ => Y t / (1 - t)) (Icc (-1 : ℝ) 1) := by
    by_contra h
    have hw : 0 < secondUnscaledFlatHalfWidth := secondFreeArc_endpoints.1
    change 0 < Real.pi⁻¹ * (∫ t in Icc (-1 : ℝ) 1, Y t / (1 - t)) at hw
    rw [integral_undef h, mul_zero] at hw
    exact lt_irrefl _ hw
  have hi : IntegrableOn (fun t : ℝ => Y t * (1 + t)) (Icc (-1 : ℝ) 1) :=
    (hc.mul (continuous_const.add continuous_id)).integrableOn_Icc
  have hweight : (∫ t in Icc (-1 : ℝ) 1, Y t * (1 + t)) = secondMoments.M := by
    rw [pair_integrable_interval hi, secondMass_eq_twice_integral,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    change Y t * (1 + t) + Y (-t) * (1 + -t) = 2 * Y t
    rw [show Y (-t) = Y t from height_even secondEigenfunction t]
    ring
  have hm : secondMoments.M ≤ ∫ t in Icc (-1 : ℝ) 1, Y t / (1 - t) := by
    rw [← hweight]
    apply setIntegral_mono_on hi hquot measurableSet_Icc
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · apply (le_div_iff₀ (sub_pos.mpr hlt)).2
      nlinarith [mul_nonneg (hnn t) (sq_nonneg t)]
    · change height secondEigenfunction 1 * _ ≤ height secondEigenfunction 1 / _
      rw [height_zero_of_one_le_abs _ (by norm_num : (1 : ℝ) ≤ |1|)]
      simp
  change secondMoments.M / Real.pi ≤ Real.pi⁻¹ * _
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr Real.pi_pos.le)

/-- The physical half-width of the area-one optimizer is at least its
maximizing inward slope divided by π. -/
theorem sharpConstant_div_pi_le_normalizedFlatHalfWidth :
    spectralConstant secondEigenvalue secondEigenfunction / Real.pi ≤ normalizedFlatHalfWidth := by
  have hN : secondMoments.N ≤ height secondEigenfunction 0 * secondMoments.M :=
    squareMass_le_height_zero_mul_mass secondEigenfunction_continuous.continuousOn
      (nonneg_on_unitInterval_of_odd_positive secondEigenfunction_odd
        secondEigenfunction_zero_exterior secondEigenfunction_pos)
  have hq : secondMoments.flux ≤ height secondEigenfunction 0 / 2 := by
    rw [secondMoments.flux_eq]
    apply (div_le_iff₀ (mul_pos (by norm_num) secondMoments.M_pos)).2
    linarith
  have hqm : secondMoments.flux ≤ secondMoments.M := by
    linarith [secondHeight_zero_le_three_halves_mass, secondMoments.M_pos]
  have hwidth := (div_le_div_of_nonneg_right hqm Real.pi_pos.le).trans
    secondMass_div_pi_le_flatHalfWidth
  change secondMoments.sharpConstant / Real.pi ≤ (Real.sqrt secondMoments.area)⁻¹ * _
  rw [← secondMoments.normalized_flux_eq]
  calc
    secondMoments.flux / Real.sqrt secondMoments.area / Real.pi =
        (Real.sqrt secondMoments.area)⁻¹ * (secondMoments.flux / Real.pi) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwidth (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- Every point of the quantitative closed patch centered at the maximizing
midpoint is on the actual frontier of the normalized optimizer. -/
theorem normalizedFlatPatch_of_abs_le_sharpConstant_div_pi {x : ℝ}
    (hx : |x| ≤ spectralConstant secondEigenvalue secondEigenfunction / Real.pi) :
    (x : ℂ) ∈ frontier (normalizedImage secondEigenvalue secondEigenfunction) :=
  (real_mem_frontier_normalizedImage_iff x).2
    (hx.trans sharpConstant_div_pi_le_normalizedFlatHalfWidth)

end Torsion.Spectral

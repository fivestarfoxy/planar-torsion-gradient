import Torsion.RestrictedSpectralSymmetry
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# An explicit odd polynomial trial and its exact ordinary energies

These calculations concern the genuine zero extension. Admission to the
restricted half-derivative form and its fractional Rayleigh bound are proved
separately, using smooth core approximations and Fourier interpolation.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

def oddTrialPolynomial (x : ℝ) : ℝ := x * (1 - x ^ 2) * (1 - x ^ 2 / 2)

def oddTrial (x : ℝ) : ℝ := (Icc (-1 : ℝ) 1).indicator oddTrialPolynomial x

def oddTrialDerivative (x : ℝ) : ℝ :=
  (Icc (-1 : ℝ) 1).indicator (fun x => 1 - (9 / 2 : ℝ) * x ^ 2 + (5 / 2 : ℝ) * x ^ 4) x

theorem oddTrialPolynomial_hasDerivAt (x : ℝ) :
    HasDerivAt oddTrialPolynomial (1 - (9 / 2 : ℝ) * x ^ 2 + (5 / 2 : ℝ) * x ^ 4) x := by
  convert ((hasDerivAt_id x).mul ((hasDerivAt_const x 1).sub (hasDerivAt_pow 2 x))).mul
    ((hasDerivAt_const x 1).sub ((hasDerivAt_pow 2 x).div_const 2)) using 1
  all_goals dsimp only [oddTrialPolynomial, id_eq]
  all_goals ring

theorem oddTrialPolynomial_contDiff : ContDiff ℝ ∞ oddTrialPolynomial := by
  exact (contDiff_id.mul (contDiff_const.sub (contDiff_id.pow 2))).mul
    (contDiff_const.sub ((contDiff_id.pow 2).div_const 2))

theorem oddTrial_odd : Function.Odd oddTrial := by
  intro x
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have hnx : -x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    simp only [oddTrial, indicator_of_mem hx, indicator_of_mem hnx, oddTrialPolynomial]
    ring
  · have hnx : -x ∉ Icc (-1 : ℝ) 1 := by
      intro h
      apply hx
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
    simp only [oddTrial, indicator_of_not_mem hx, indicator_of_not_mem hnx, neg_zero]

theorem oddTrial_eq_max (x : ℝ) :
    oddTrial x = x * max (1 - x ^ 2) 0 * (1 - x ^ 2 / 2) := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have hs : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 (abs_le.2 hx)
    simp only [oddTrial, indicator_of_mem hx, oddTrialPolynomial,
      max_eq_left (by linarith : 0 ≤ 1 - x ^ 2)]
  · have hs : 1 ≤ x ^ 2 := by
      have ha : 1 ≤ |x| := le_of_not_ge fun h => hx (abs_le.1 h)
      nlinarith [sq_abs x]
    simp only [oddTrial, indicator_of_not_mem hx,
      max_eq_right (by linarith : 1 - x ^ 2 ≤ 0), mul_zero, zero_mul]

theorem oddTrial_continuous : Continuous oddTrial := by
  have heq : oddTrial = fun x => x * max (1 - x ^ 2) 0 * (1 - x ^ 2 / 2) :=
    funext oddTrial_eq_max
  rw [heq]
  fun_prop

theorem oddTrial_hasCompactSupport : HasCompactSupport oddTrial := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-1 : ℝ) 1) isCompact_Icc
  intro x hx
  by_contra hn
  exact hx (by simp only [oddTrial, indicator_of_not_mem hn])

theorem oddTrial_memLp : MemLp oddTrial 2 volume :=
  oddTrial_continuous.memLp_of_hasCompactSupport oddTrial_hasCompactSupport

theorem oddTrial_integrable : Integrable oddTrial :=
  oddTrial_continuous.integrable_of_hasCompactSupport oddTrial_hasCompactSupport

theorem oddTrialDerivative_memLp : MemLp oddTrialDerivative 2 volume := by
  have hc : Continuous (fun x : ℝ => 1 - (9 / 2 : ℝ) * x ^ 2 + (5 / 2 : ℝ) * x ^ 4) := by
    fun_prop
  apply (memLp_two_iff_integrable_sq
    (hc.aestronglyMeasurable.indicator measurableSet_Icc)).2
  have hi := (hc.pow 2).integrableOn_Icc (μ := (volume : Measure ℝ)) (a := (-1 : ℝ)) (b := 1)
  have heq : (fun x : ℝ => oddTrialDerivative x ^ 2) =
      (Icc (-1 : ℝ) 1).indicator
        (fun x => (1 - (9 / 2 : ℝ) * x ^ 2 + (5 / 2 : ℝ) * x ^ 4) ^ 2) := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1 <;> simp [oddTrialDerivative, hx]
  change Integrable (fun x => oddTrialDerivative x ^ 2)
  rw [heq]
  exact (integrable_indicator_iff measurableSet_Icc).2 hi

theorem oddTrial_integral_sq : (∫ x : ℝ, oddTrial x ^ 2) = 124 / 1155 := by
  have heq : (fun x : ℝ => oddTrial x ^ 2) =
      (Icc (-1 : ℝ) 1).indicator (fun x => oddTrialPolynomial x ^ 2) := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1 <;> simp [oddTrial, hx]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  let A : ℝ → ℝ := fun x => x ^ 3 / 3 - (3 / 5 : ℝ) * x ^ 5 +
    (13 / 28 : ℝ) * x ^ 7 - x ^ 9 / 6 + x ^ 11 / 44
  have hdA (x : ℝ) : HasDerivAt A (oddTrialPolynomial x ^ 2) x := by
    convert (((((hasDerivAt_pow 3 x).div_const 3).sub
      ((hasDerivAt_pow 5 x).const_mul (3 / 5 : ℝ))).add
      ((hasDerivAt_pow 7 x).const_mul (13 / 28 : ℝ))).sub
      ((hasDerivAt_pow 9 x).div_const 6)).add ((hasDerivAt_pow 11 x).div_const 44) using 1
    all_goals dsimp only [A, oddTrialPolynomial]
    all_goals ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hdA x) ((oddTrialPolynomial_contDiff.continuous.pow 2).intervalIntegrable _ _)]
  norm_num [A]

theorem oddTrialDerivative_integral_sq : (∫ x : ℝ, oddTrialDerivative x ^ 2) = 334 / 315 := by
  have heq : (fun x : ℝ => oddTrialDerivative x ^ 2) =
      (Icc (-1 : ℝ) 1).indicator
        (fun x => (1 - (9 / 2 : ℝ) * x ^ 2 + (5 / 2 : ℝ) * x ^ 4) ^ 2) := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1 <;> simp [oddTrialDerivative, hx]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  let A : ℝ → ℝ := fun x => x - 3 * x ^ 3 + (101 / 20 : ℝ) * x ^ 5 -
    (45 / 14 : ℝ) * x ^ 7 + (25 / 36 : ℝ) * x ^ 9
  have hdA (x : ℝ) : HasDerivAt A
      ((1 - (9 / 2 : ℝ) * x ^ 2 + (5 / 2 : ℝ) * x ^ 4) ^ 2) x := by
    convert (((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).const_mul 3)).add
      ((hasDerivAt_pow 5 x).const_mul (101 / 20 : ℝ))).sub
      ((hasDerivAt_pow 7 x).const_mul (45 / 14 : ℝ))).add
      ((hasDerivAt_pow 9 x).const_mul (25 / 36 : ℝ))) using 1
    all_goals dsimp only [A]
    all_goals ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hdA x)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num [A]

end Torsion.Spectral

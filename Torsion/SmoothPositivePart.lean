import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Flat smooth approximations to the positive part

The primitive of `Real.smoothTransition ((n+1)t)` is smooth, fixes zero, and
has derivative between zero and one. Its derivative is zero at zero at every
stage, so the limiting Sobolev chain rule does not require a separate claim
about the weak gradient on a zero level set.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion.SmoothPositivePart

/-- A smooth approximation to the derivative of the positive part. -/
def slope (n : ℕ) (t : ℝ) : ℝ := Real.smoothTransition (((n : ℝ) + 1) * t)

/-- A smooth approximation to `max t 0`, obtained by integrating the flat
smooth transition rather than rounding the corner symmetrically. -/
def approx (n : ℕ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, slope n s

theorem slope_contDiff (n : ℕ) : ContDiff ℝ ∞ (slope n) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)

theorem slope_nonneg (n : ℕ) (t : ℝ) : 0 ≤ slope n t :=
  Real.smoothTransition.nonneg _

theorem slope_le_one (n : ℕ) (t : ℝ) : slope n t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem slope_norm_le_one (n : ℕ) (t : ℝ) : ‖slope n t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (slope_nonneg n t)]
  exact slope_le_one n t

@[simp] theorem slope_zero (n : ℕ) : slope n 0 = 0 := by simp [slope]

@[simp] theorem approx_zero (n : ℕ) : approx n 0 = 0 := by simp [approx]

theorem approx_hasDerivAt (n : ℕ) (t : ℝ) : HasDerivAt (approx n) (slope n t) t := by
  have hc := (slope_contDiff n).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

@[simp] theorem approx_deriv (n : ℕ) (t : ℝ) : deriv (approx n) t = slope n t :=
  (approx_hasDerivAt n t).deriv

theorem approx_contDiff (n : ℕ) : ContDiff ℝ ∞ (approx n) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (approx_hasDerivAt n t).differentiableAt, ?_⟩
  have heq : deriv (approx n) = slope n := funext (approx_deriv n)
  rw [heq]
  exact slope_contDiff n

theorem approx_lipschitz (n : ℕ) : LipschitzWith 1 (approx n) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (approx_hasDerivAt n t).differentiableAt)
  intro t
  rw [approx_deriv]
  exact_mod_cast slope_norm_le_one n t

/-- The approximants obey the same linear domination as the positive part. -/
theorem approx_norm_le (n : ℕ) (t : ℝ) : ‖approx n t‖ ≤ ‖t‖ := by
  simpa only [dist_eq_norm, approx_zero, sub_zero, NNReal.coe_one, one_mul] using
    (approx_lipschitz n).dist_le_mul t 0

theorem slope_zero_of_nonpos (n : ℕ) {t : ℝ} (ht : t ≤ 0) : slope n t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) ht

/-- Each smooth approximant is identically zero on the negative half-line. -/
theorem approx_zero_of_nonpos (n : ℕ) {t : ℝ} (ht : t ≤ 0) : approx n t = 0 := by
  unfold approx
  have heq : (∫ s in (0 : ℝ)..t, slope n s) = ∫ s in (0 : ℝ)..t, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    apply Eventually.of_forall
    intro s hs
    rw [uIoc_of_ge ht] at hs
    exact slope_zero_of_nonpos n hs.2
  simpa using heq

theorem approx_nonneg (n : ℕ) (t : ℝ) : 0 ≤ approx n t := by
  by_cases ht : 0 ≤ t
  · exact intervalIntegral.integral_nonneg_of_forall ht (slope_nonneg n)
  · rw [approx_zero_of_nonpos n (le_of_not_ge ht)]

/-- The derivative converges to the positive-half-line indicator, with its
value at zero equal to zero at every stage. -/
theorem tendsto_slope (t : ℝ) :
    Tendsto (fun n => slope n t) atTop (𝓝 (if 0 < t then (1 : ℝ) else 0)) := by
  by_cases ht : 0 < t
  · rw [if_pos ht]
    have hevent : (fun n => slope n t) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / t)
      filter_upwards [eventually_ge_atTop N] with n hn
      apply Real.smoothTransition.one_of_one_le
      have hnreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hNt : 1 < (N : ℝ) * t := (div_lt_iff₀ ht).mp hN
      nlinarith
    exact (tendsto_congr' hevent).2 tendsto_const_nhds
  · rw [if_neg ht]
    have heq : (fun n => slope n t) = (fun _ => (0 : ℝ)) :=
      funext (fun n => slope_zero_of_nonpos n (le_of_not_gt ht))
    rw [heq]
    exact tendsto_const_nhds

private theorem integral_positive_indicator (t : ℝ) :
    (∫ s in (0 : ℝ)..t, if 0 < s then (1 : ℝ) else 0) = max t 0 := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht]
    have heq : (∫ s in (0 : ℝ)..t, if 0 < s then (1 : ℝ) else 0) =
        ∫ s in (0 : ℝ)..t, (1 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      apply Eventually.of_forall
      intro s hs
      rw [uIoc_of_le ht] at hs
      exact if_pos hs.1
    simpa using heq
  · have hnonpos : t ≤ 0 := le_of_not_ge ht
    rw [max_eq_right hnonpos]
    have heq : (∫ s in (0 : ℝ)..t, if 0 < s then (1 : ℝ) else 0) =
        ∫ s in (0 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      apply Eventually.of_forall
      intro s hs
      rw [uIoc_of_ge hnonpos] at hs
      exact if_neg (not_lt.mpr hs.2)
    simpa using heq

/-- The primitives converge pointwise to the positive part, proved by
Lebesgue dominated convergence on the actual finite integration interval. -/
theorem tendsto_approx (t : ℝ) :
    Tendsto (fun n => approx n t) atTop (𝓝 (max t 0)) := by
  have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := (0 : ℝ)) (b := t) (μ := volume) (F := slope)
    (f := fun s => if 0 < s then (1 : ℝ) else 0) (fun _ => (1 : ℝ))
    (Eventually.of_forall (fun n => (slope_contDiff n).continuous.aestronglyMeasurable))
    (Eventually.of_forall (fun n => Eventually.of_forall (fun s _ => slope_norm_le_one n s)))
    intervalIntegrable_const
    (Eventually.of_forall (fun s _ => tendsto_slope s))
  simpa only [approx, integral_positive_indicator] using hlim

end Torsion.SmoothPositivePart

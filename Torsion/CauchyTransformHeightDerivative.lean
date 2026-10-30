import Torsion.SpectralPositivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.MetricSpace.Holder

/-!
# The derivative of the integrated odd profile

This proves the concrete identity `Y' = -φ`, including the origin and the
support endpoints, from continuity, oddness and zero exterior values.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Torsion.Spectral

/-- The height has compact support regardless of the input function. -/
theorem height_hasCompactSupport (φ : ℝ → ℝ) : HasCompactSupport (height φ) := by
  apply HasCompactSupport.intro (K := Icc (-1 : ℝ) 1) isCompact_Icc
  intro x hx
  have hnot : ¬ |x| < 1 := by
    intro h
    exact hx (abs_le.1 h.le)
  simp [height, hnot]

theorem height_integrable {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) : Integrable (height φ) :=
  (height_continuous hφ).integrable_of_hasCompactSupport (height_hasCompactSupport φ)

private theorem integral_odd_primitive_even {φ : ℝ → ℝ} (hodd : Function.Odd φ) (x : ℝ) :
    (∫ s in (0 : ℝ)..(-x), φ s) = ∫ s in (0 : ℝ)..x, φ s := by
  calc
    (∫ s in (0 : ℝ)..(-x), φ s) = -(∫ s in (-x)..(0 : ℝ), φ s) :=
      intervalIntegral.integral_symm _ _
    _ = -(∫ s in (0 : ℝ)..x, φ (-s)) := by
      rw [intervalIntegral.integral_comp_neg, neg_zero]
    _ = ∫ s in (0 : ℝ)..x, φ s := by
      have hp : ∀ s : ℝ, φ (-s) = -φ s := hodd
      simp only [hp, intervalIntegral.integral_neg, neg_neg]

private theorem integral_from_abs_eq {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ) (x : ℝ) :
    (∫ s in |x|..(1 : ℝ), φ s) = ∫ s in x..(1 : ℝ), φ s := by
  have h₁ : (∫ s in (0 : ℝ)..|x|, φ s) + (∫ s in |x|..(1 : ℝ), φ s) =
      ∫ s in (0 : ℝ)..(1 : ℝ), φ s := intervalIntegral.integral_add_adjacent_intervals
    (hφ.intervalIntegrable (0 : ℝ) |x|) (hφ.intervalIntegrable |x| (1 : ℝ))
  have h₂ : (∫ s in (0 : ℝ)..x, φ s) + (∫ s in x..(1 : ℝ), φ s) =
      ∫ s in (0 : ℝ)..(1 : ℝ), φ s := intervalIntegral.integral_add_adjacent_intervals
    (hφ.intervalIntegrable (0 : ℝ) x) (hφ.intervalIntegrable x (1 : ℝ))
  have hprim : (∫ s in (0 : ℝ)..|x|, φ s) = ∫ s in (0 : ℝ)..x, φ s := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx), integral_odd_primitive_even hodd x]
  rw [hprim] at h₁
  linarith

/-- For continuous odd data with zero exterior values, the height is a
single ordinary primitive on all of R; no absolute-value singularity remains. -/
theorem height_eq_integral_of_odd {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (x : ℝ) :
    height φ x = ∫ s in x..(1 : ℝ), φ s := by
  rw [← integral_from_abs_eq hφ hodd x]
  by_cases hx : |x| < 1
  · rw [height, if_pos hx, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx.le]
  · rw [height, if_neg hx]
    have hle : 1 ≤ |x| := le_of_not_gt hx
    have hint : (∫ s in (1 : ℝ)..|x|, φ s) = 0 := by
      calc
        (∫ s in (1 : ℝ)..|x|, φ s) = ∫ s in (1 : ℝ)..|x|, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le hle] at hs
          exact hzero s (hs.1.trans (le_abs_self s))
        _ = 0 := by simp
    rw [intervalIntegral.integral_symm, hint, neg_zero]

/-- The actual FTC identity from Lemma 5.1, valid at every real point. -/
theorem hasDerivAt_height {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (x : ℝ) :
    HasDerivAt (height φ) (-φ x) x := by
  have heq : height φ = fun u : ℝ => ∫ s in u..(1 : ℝ), φ s :=
    funext (height_eq_integral_of_odd hφ hodd hzero)
  rw [heq]
  exact intervalIntegral.integral_hasDerivAt_left (hφ.intervalIntegrable x (1 : ℝ))
    (hφ.stronglyMeasurableAtFilter volume (𝓝 x)) hφ.continuousAt

theorem deriv_height_eq {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (x : ℝ) :
    deriv (height φ) x = -φ x :=
  (hasDerivAt_height hφ hodd hzero x).deriv

/-- The integrated zero-extended odd profile is globally C¹. The Hölder
regularity of its derivative reduces to that of the original eigenfunction. -/
theorem height_contDiff_one {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    ContDiff ℝ 1 (height φ) := by
  apply contDiff_one_iff_deriv.2
  constructor
  · intro x
    exact (hasDerivAt_height hφ hodd hzero x).differentiableAt
  · have heq : deriv (height φ) = fun x => -φ x :=
      funext (deriv_height_eq hφ hodd hzero)
    rw [heq]
    exact hφ.neg

/-- The Hölder estimate transfers exactly from φ to Y', giving the
`C^(1,α)` regularity claimed for the integrated profile. -/
theorem height_deriv_holder {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {C r : NNReal} (hh : HolderWith C r φ) :
    HolderWith C r (deriv (height φ)) := by
  intro x y
  rw [deriv_height_eq hφ hodd hzero x, deriv_height_eq hφ hodd hzero y]
  simpa only [edist_neg_neg] using hh x y

end Torsion.Spectral

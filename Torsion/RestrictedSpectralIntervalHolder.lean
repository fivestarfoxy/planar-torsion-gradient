module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! The elementary one-half Hölder estimate for an actual L² primitive. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Torsion.Spectral

private theorem integral_mul_sq_le {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have heq {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    simp [hfx, hgx, RCLike.inner_apply, mul_comm]
  simpa only [heq hf hg, heq hf hf, heq hg hg, ← sq] using
    real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)

/-- A globally L² function is integrable on every finite interval. -/
theorem _root_.MeasureTheory.MemLp.intervalIntegrable_of_two {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (a b : ℝ) : IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_iff' (by finiteness)).mpr
  change Integrable f (volume.restrict (Icc (min a b) (max a b)))
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hf.restrict _)

/-- Cauchy--Schwarz for the ordinary signed interval integral, with the
original global square integral as its constant. -/
theorem _root_.MeasureTheory.MemLp.intervalIntegral_sq_le {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (a b : ℝ) :
    (∫ x in a..b, f x) ^ 2 ≤ (∫ x : ℝ, f x ^ 2) * |b - a| := by
  suffices hle : ∀ a b : ℝ, a ≤ b →
      (∫ x in a..b, f x) ^ 2 ≤ (∫ x : ℝ, f x ^ 2) * (b - a) by
    rcases le_total a b with hab | hba
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hle a b hab
    · rw [intervalIntegral.integral_symm, neg_sq, abs_of_nonpos (sub_nonpos.mpr hba)]
      simpa only [neg_sub] using hle b a hba
  intro a b hab
  have hg : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Icc a b)) := by
    exact memLp_const (1 : ℝ)
  have hCS := integral_mul_sq_le (hf.restrict (Icc a b)) hg
  simp only [mul_one, one_pow, setIntegral_const, smul_eq_mul, mul_one,
    Real.volume_real_Icc_of_le hab] at hCS
  have hmono : (∫ x in Icc a b, f x ^ 2) ≤ ∫ x : ℝ, f x ^ 2 :=
    setIntegral_le_integral hf.integrable_sq (ae_of_all _ fun x => sq_nonneg _)
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact hCS.trans (mul_le_mul_of_nonneg_right hmono (sub_nonneg.mpr hab))

/-- Every actual L² primitive satisfies a global one-half Hölder estimate. -/
theorem _root_.MeasureTheory.MemLp.abs_intervalIntegral_le_sqrt {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (a b : ℝ) :
    |∫ x in a..b, f x| ≤ Real.sqrt (∫ x : ℝ, f x ^ 2) * Real.sqrt |b - a| := by
  have h := hf.intervalIntegral_sq_le a b
  have habs : |∫ x in a..b, f x| ^ 2 ≤ (∫ x : ℝ, f x ^ 2) * |b - a| := by
    simpa only [sq_abs] using h
  have hs := Real.le_sqrt_of_sq_le habs
  rwa [Real.sqrt_mul (integral_nonneg fun x => sq_nonneg _)] at hs

end Torsion.Spectral

import Torsion.RestrictedSpectralParseval
import Torsion.RestrictedSpectralEvenFourierBounds
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Real.Pi.Bounds

/-!
# A quantitative Fourier gap for even functions of mean zero

Explicit pointwise Fourier bounds, integrated against a piecewise polynomial
frequency weight, separate the next even level from the odd trial level.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

private theorem integral_abs_pow_symmetric (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (∫ x in Icc (-a) a, |x| ^ n) = 2 * (a ^ (n + 1) / (n + 1)) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
  have hc : IntervalIntegrable (fun x : ℝ => |x| ^ n) volume (-a) 0 :=
    (continuous_abs.pow n).intervalIntegrable _ _
  have hd : IntervalIntegrable (fun x : ℝ => |x| ^ n) volume 0 a :=
    (continuous_abs.pow n).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hc hd]
  have hleft : (∫ x in -a..(0 : ℝ), |x| ^ n) = ∫ x in (0 : ℝ)..a, x ^ n := by
    calc
      _ = ∫ x in (0 : ℝ)..a, |-x| ^ n := by
        simpa only [neg_neg, neg_zero] using
          (intervalIntegral.integral_comp_neg (f := fun x : ℝ => |x| ^ n) (a := 0) (b := a)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : 0 ≤ x := by simpa only [min_eq_left ha] using hx.1
        simp only [abs_neg, abs_of_nonneg hx']
  have hright : (∫ x in (0 : ℝ)..a, |x| ^ n) = ∫ x in (0 : ℝ)..a, x ^ n := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : 0 ≤ x := by simpa only [min_eq_left ha] using hx.1
    simp only [abs_of_nonneg hx']
  rw [hleft, hright, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero n), sub_zero]
  ring

private theorem integral_tent_pow (a R : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (∫ x in Icc (-a) a, (R - |x|) * |x| ^ n) =
      2 * (R * (a ^ (n + 1) / (n + 1)) - a ^ (n + 2) / (n + 2)) := by
  have hc : IntegrableOn (fun x : ℝ => R * |x| ^ n) (Icc (-a) a) :=
    (continuous_const.mul (continuous_abs.pow n)).integrableOn_Icc
  have hd : IntegrableOn (fun x : ℝ => |x| ^ (n + 1)) (Icc (-a) a) :=
    (continuous_abs.pow (n + 1)).integrableOn_Icc
  calc
    _ = ∫ x in Icc (-a) a, R * |x| ^ n - |x| ^ (n + 1) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [pow_succ]
      ring
    _ = _ := by
      rw [integral_sub hc hd, integral_const_mul,
        integral_abs_pow_symmetric a ha n, integral_abs_pow_symmetric a ha (n + 1)]
      push_cast
      ring

private def evenGapWeight (ξ : ℝ) : ℝ :=
  (Icc (-(9 / 4 : ℝ)) (9 / 4)).indicator
    (fun ξ => ((9 / 2 : ℝ) - |ξ|) * ((28 / 625 : ℝ) * |ξ| ^ 4 - 9 / 8)) ξ +
  (Icc (-(9 / 2 : ℝ)) (9 / 2)).indicator
    (fun ξ => ((9 / 2 : ℝ) - |ξ|) * (9 / 8)) ξ

private theorem integrable_evenGapWeight : Integrable evenGapWeight := by
  unfold evenGapWeight
  apply Integrable.add
  · apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact ((continuous_const.sub continuous_abs).mul
      ((continuous_const.mul (continuous_abs.pow 4)).sub continuous_const)).integrableOn_Icc
  · apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact ((continuous_const.sub continuous_abs).mul continuous_const).integrableOn_Icc

private theorem integral_evenGapWeight : (∫ ξ : ℝ, evenGapWeight ξ) = 26905203 / 3200000 := by
  have hp : IntegrableOn
      (fun ξ : ℝ => ((9 / 2 : ℝ) - |ξ|) * ((28 / 625 : ℝ) * |ξ| ^ 4 - 9 / 8))
      (Icc (-(9 / 4 : ℝ)) (9 / 4)) :=
    ((continuous_const.sub continuous_abs).mul
      ((continuous_const.mul (continuous_abs.pow 4)).sub continuous_const)).integrableOn_Icc
  have hq : IntegrableOn
      (fun ξ : ℝ => ((9 / 2 : ℝ) - |ξ|) * (9 / 8))
      (Icc (-(9 / 2 : ℝ)) (9 / 2)) :=
    ((continuous_const.sub continuous_abs).mul continuous_const).integrableOn_Icc
  have hpt : (∫ ξ in Icc (-(9 / 4 : ℝ)) (9 / 4),
      ((9 / 2 : ℝ) - |ξ|) * ((28 / 625 : ℝ) * |ξ| ^ 4 - 9 / 8)) =
      (28 / 625 : ℝ) * (2 * ((9 / 2 : ℝ) * ((9 / 4 : ℝ) ^ 5 / 5) - (9 / 4 : ℝ) ^ 6 / 6)) -
      (9 / 8 : ℝ) * (2 * ((9 / 2 : ℝ) * ((9 / 4 : ℝ) ^ 1 / 1) - (9 / 4 : ℝ) ^ 2 / 2)) := by
    have hi4 : IntegrableOn (fun ξ : ℝ => ((9 / 2 : ℝ) - |ξ|) * |ξ| ^ 4)
        (Icc (-(9 / 4 : ℝ)) (9 / 4)) :=
      ((continuous_const.sub continuous_abs).mul (continuous_abs.pow 4)).integrableOn_Icc
    have hi0 : IntegrableOn (fun ξ : ℝ => ((9 / 2 : ℝ) - |ξ|) * |ξ| ^ 0)
        (Icc (-(9 / 4 : ℝ)) (9 / 4)) :=
      ((continuous_const.sub continuous_abs).mul (continuous_abs.pow 0)).integrableOn_Icc
    calc
      _ = ∫ ξ in Icc (-(9 / 4 : ℝ)) (9 / 4),
          (28 / 625 : ℝ) * (((9 / 2 : ℝ) - |ξ|) * |ξ| ^ 4) -
          (9 / 8 : ℝ) * (((9 / 2 : ℝ) - |ξ|) * |ξ| ^ 0) := by
        congr 1
        funext ξ
        ring
      _ = _ := by
        rw [integral_sub (hi4.const_mul _) (hi0.const_mul _), integral_const_mul,
          integral_const_mul, integral_tent_pow _ _ (by norm_num) 4,
          integral_tent_pow _ _ (by norm_num) 0]
        norm_num
  have hqt : (∫ ξ in Icc (-(9 / 2 : ℝ)) (9 / 2),
      ((9 / 2 : ℝ) - |ξ|) * (9 / 8)) = (9 / 8 : ℝ) *
      (2 * ((9 / 2 : ℝ) * ((9 / 2 : ℝ) ^ 1 / 1) - (9 / 2 : ℝ) ^ 2 / 2)) := by
    calc
      _ = (9 / 8 : ℝ) * ∫ ξ in Icc (-(9 / 2 : ℝ)) (9 / 2),
          ((9 / 2 : ℝ) - |ξ|) * |ξ| ^ 0 := by
        rw [← integral_const_mul]
        congr 1
        funext ξ
        ring
      _ = _ := by rw [integral_tent_pow _ _ (by norm_num) 0]; norm_num
  unfold evenGapWeight
  rw [integral_add ((integrable_indicator_iff measurableSet_Icc).mpr hp)
    ((integrable_indicator_iff measurableSet_Icc).mpr hq),
    integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc, hpt, hqt]
  norm_num

/-- An explicit frequency integration estimate. Both premises are
pointwise bounds on the original Fourier integral, with the actual source
L² mass. -/
private theorem energy_ge_of_even_fourier_bounds {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f)
    (hlow : ∀ ξ : ℝ, ‖fourier f ξ‖ ^ 2 ≤
      (28 / 625 : ℝ) * ξ ^ 4 * (∫ x : ℝ, f x ^ 2))
    (hhigh : ∀ ξ : ℝ, ‖fourier f ξ‖ ^ 2 ≤
      (9 / 8 : ℝ) * (∫ x : ℝ, f x ^ 2)) :
    (63 / 20 : ℝ) * (∫ x : ℝ, f x ^ 2) ≤ energy f f := by
  let M : ℝ := ∫ x : ℝ, f x ^ 2
  let Ψ : ℝ → ℝ := fun ξ => ‖fourier f ξ‖ ^ 2
  let W : ℝ → ℝ := fun ξ => |ξ| * Ψ ξ
  have hM : 0 ≤ M := integral_nonneg fun x => sq_nonneg _
  have hΨ : Integrable Ψ :=
    (memLp_two_iff_integrable_sq_norm hf.fourier_parseval.1.1).mp hf.fourier_parseval.1
  have hW : Integrable W := hf.2.1
  have hpoint (ξ : ℝ) : (9 / 2 : ℝ) * Ψ ξ ≤
      W ξ + evenGapWeight ξ * M := by
    have hnonneg : 0 ≤ Ψ ξ := sq_nonneg _
    by_cases hsmall : ξ ∈ Icc (-(9 / 4 : ℝ)) (9 / 4)
    · have hbig : ξ ∈ Icc (-(9 / 2 : ℝ)) (9 / 2) := by
        constructor <;> linarith [hsmall.1, hsmall.2]
      have habs : |ξ| ≤ (9 / 4 : ℝ) := abs_le.2 hsmall
      have hfactor : 0 ≤ (9 / 2 : ℝ) - |ξ| := by linarith
      have hcap : Ψ ξ ≤ (28 / 625 : ℝ) * |ξ| ^ 4 * M := by
        simpa only [Ψ, M, pow_abs, abs_of_nonneg (by positivity : 0 ≤ ξ ^ 4)] using hlow ξ
      have hmul := mul_le_mul_of_nonneg_left hcap hfactor
      simp only [evenGapWeight, indicator_of_mem hsmall, indicator_of_mem hbig]
      dsimp only [W]
      nlinarith only [hmul]
    · by_cases hbig : ξ ∈ Icc (-(9 / 2 : ℝ)) (9 / 2)
      · have habs : |ξ| ≤ (9 / 2 : ℝ) := abs_le.2 hbig
        have hfactor : 0 ≤ (9 / 2 : ℝ) - |ξ| := by linarith
        have hmul := mul_le_mul_of_nonneg_left (hhigh ξ) hfactor
        simp only [evenGapWeight, indicator_of_not_mem hsmall, indicator_of_mem hbig, zero_add]
        dsimp only [W, Ψ, M] at *
        nlinarith only [hmul]
      · have habs : (9 / 2 : ℝ) ≤ |ξ| :=
          le_of_not_ge (fun h => hbig (abs_le.1 h))
        simp only [evenGapWeight, indicator_of_not_mem hsmall,
          indicator_of_not_mem hbig, zero_add, zero_mul, add_zero]
        dsimp only [W]
        exact mul_le_mul_of_nonneg_right habs hnonneg
  have hIntegral := integral_mono (hΨ.const_mul (9 / 2 : ℝ))
    (hW.add (integrable_evenGapWeight.mul_const M)) hpoint
  have hmass : (∫ ξ : ℝ, Ψ ξ) = (2 * Real.pi) * M := hf.fourier_parseval.2
  have henergy : (∫ ξ : ℝ, W ξ) = (2 * Real.pi) * energy f f := by
    rw [energy_self]
    dsimp only [W, Ψ]
    field_simp [Real.pi_ne_zero]
  change (∫ ξ : ℝ, (9 / 2 : ℝ) * Ψ ξ) ≤
    ∫ ξ : ℝ, W ξ + evenGapWeight ξ * M at hIntegral
  rw [integral_const_mul, integral_add hW (integrable_evenGapWeight.mul_const M),
    integral_mul_const, integral_evenGapWeight, hmass, henergy] at hIntegral
  have hconstant : (9 / 2 : ℝ) * (2 * Real.pi) - 26905203 / 3200000 ≥
      (2 * Real.pi) * (63 / 20 : ℝ) := by
    nlinarith [Real.pi_gt_d2]
  have hmul := mul_le_mul_of_nonneg_right hconstant hM
  nlinarith only [hIntegral, hmul, Real.pi_pos]

/-- Every actual even restricted form member of mean zero lies above a
fixed rational level strictly greater than `π`. This is an estimate for
the original Fourier quadratic form on its original domain. -/
theorem MemRestrictedFormDomain.even_mean_zero_energy_ge {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (heven : Function.Even f)
    (hmean : ∫ x : ℝ, f x = 0) :
    (63 / 20 : ℝ) * (∫ x : ℝ, f x ^ 2) ≤ energy f f :=
  energy_ge_of_even_fourier_bounds hf
    (hf.norm_fourier_sq_le_even_mean_zero_polynomial heven hmean)
    (hf.norm_fourier_sq_le_even_mean_zero_uniform heven hmean)

/-- The preceding rational level is strictly greater than `π`. -/
theorem MemRestrictedFormDomain.pi_mul_integral_sq_lt_energy_of_even_mean_zero
    {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) (heven : Function.Even f)
    (hmean : ∫ x : ℝ, f x = 0) (hpos : 0 < ∫ x : ℝ, f x ^ 2) :
    Real.pi * (∫ x : ℝ, f x ^ 2) < energy f f := by
  have hπ : Real.pi < (63 / 20 : ℝ) := by linarith [Real.pi_lt_d2]
  exact (mul_lt_mul_of_pos_right hπ hpos).trans_le (hf.even_mean_zero_energy_ge heven hmean)

end Torsion.Spectral

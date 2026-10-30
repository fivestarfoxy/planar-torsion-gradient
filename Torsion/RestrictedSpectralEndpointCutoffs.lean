module

public import Torsion.RestrictedSpectralEndpointCutoffBasic
public import Torsion.RestrictedSpectralCompactSmoothInterpolation
public import Torsion.RestrictedSpectralWeakEnergyLimit
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vanishing endpoint cutoffs in the original Fourier form

The cutoffs have value square integral of order `1/n` and derivative square
integral of order `n`. Actual Fourier interpolation therefore gives a
uniform half-energy bound. Their actual L¹ norm tends to zero, so their
energy pairing with each fixed finite-energy function tends to zero.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

private theorem integral_le_length_mul_of_support_bound {f : ℝ → ℝ} (hf : Integrable f)
    {l r M : ℝ} (hlr : l ≤ r) (hzero : ∀ x, x ∉ Icc l r → f x = 0)
    (hbound : ∀ x ∈ Icc l r, f x ≤ M) :
    (∫ x : ℝ, f x) ≤ (r - l) * M := by
  have hB : Integrable ((Icc l r).indicator (fun _ : ℝ => M)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc
  have h := integral_mono hf hB (fun x => by
    by_cases hx : x ∈ Icc l r
    · simpa only [indicator_of_mem hx] using hbound x hx
    · simp only [hzero x hx, indicator_of_notMem hx, le_refl])
  rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc_of_le hlr] at h
  simpa only [smul_eq_mul] using h

private theorem endpointCutoff_zero_off (ψ : ℝ → ℝ) (e : ℝ) (n : ℕ) (x : ℝ)
    (hx : x ∉ Icc (e - 2 / endpointCutoffScale n) (e + 2 / endpointCutoffScale n)) :
    endpointCutoff ψ e n x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (endpointCutoff_tsupport_subset ψ e n h))

private theorem endpointCutoff_deriv_zero_off (ψ : ℝ → ℝ) (e : ℝ) (n : ℕ) (x : ℝ)
    (hx : x ∉ Icc (e - 2 / endpointCutoffScale n) (e + 2 / endpointCutoffScale n)) :
    deriv (endpointCutoff ψ e n) x = 0 := by
  by_contra hn
  exact hx (endpointCutoff_tsupport_subset ψ e n (support_deriv_subset hn))

/-- The cutoff is an actual integrable compact smooth function. -/
theorem endpointCutoff_integrable {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (e : ℝ) (n : ℕ) :
    Integrable (endpointCutoff ψ e n) :=
  (endpointCutoff_contDiff hψ e n).continuous.integrable_of_hasCompactSupport
    (endpointCutoff_hasCompactSupport ψ e n)

/-- Its energy is the original, genuinely integrable Fourier expression. -/
theorem endpointCutoff_finiteEnergy {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (e : ℝ) (n : ℕ) :
    FiniteEnergy (endpointCutoff ψ e n) :=
  finiteEnergy_of_contDiff_hasCompactSupport (endpointCutoff_contDiff hψ e n)
    (endpointCutoff_hasCompactSupport ψ e n)

private theorem endpointCutoff_norm_le {ψ : ℝ → ℝ} {A : ℝ}
    (hA : ∀ x : ℝ, ‖ψ x‖ ≤ A) (e : ℝ) (n : ℕ) (x : ℝ) :
    ‖endpointCutoff ψ e n x‖ ≤ A := by
  have hAn : 0 ≤ A := (norm_nonneg (ψ x)).trans (hA x)
  have hB : ‖endpointCutoffBump (endpointCutoffScale n * (x - e))‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg endpointCutoffBump.nonneg]
    exact endpointCutoffBump.le_one
  rw [endpointCutoff, norm_mul]
  exact (mul_le_mul_of_nonneg_left hB (norm_nonneg _)).trans ((mul_one _).trans_le (hA x))

/-- The actual L¹ norm has the explicit shrinking-support bound. -/
theorem integral_norm_endpointCutoff_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {A : ℝ}
    (hA : ∀ x : ℝ, ‖ψ x‖ ≤ A) (e : ℝ) (n : ℕ) :
    (∫ x : ℝ, ‖endpointCutoff ψ e n x‖) ≤ (4 / endpointCutoffScale n) * A := by
  have h := integral_le_length_mul_of_support_bound (endpointCutoff_integrable hψ e n).norm
    (l := e - 2 / endpointCutoffScale n) (r := e + 2 / endpointCutoffScale n) (M := A)
    (by have hrad : 0 ≤ 2 / endpointCutoffScale n := div_nonneg (by norm_num) (endpointCutoffScale_pos n).le; linarith)
    (fun x hx => by rw [endpointCutoff_zero_off ψ e n x hx, norm_zero])
    (fun x _ => endpointCutoff_norm_le hA e n x)
  convert h using 1
  ring

/-- Endpoint localization vanishes in the actual ordinary L¹ norm. -/
theorem integral_norm_endpointCutoff_tendsto_zero {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {A : ℝ} (hA : ∀ x : ℝ, ‖ψ x‖ ≤ A) (e : ℝ) :
    Tendsto (fun n => ∫ x : ℝ, ‖endpointCutoff ψ e n x‖) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => (4 / endpointCutoffScale n) * A) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 * A)
    simpa only [mul_zero, zero_mul, endpointCutoffScale, div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using h
  exact squeeze_zero (fun n => integral_nonneg fun x => norm_nonneg _)
    (fun n => integral_norm_endpointCutoff_le hψ hA e n) hlim

private theorem endpointCutoff_deriv_norm_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {A D K : ℝ} (hA : ∀ x : ℝ, ‖ψ x‖ ≤ A) (hD : ∀ x : ℝ, ‖deriv ψ x‖ ≤ D)
    (hK : ∀ x : ℝ, ‖deriv endpointCutoffBump x‖ ≤ K) (e : ℝ) (n : ℕ) (x : ℝ) :
    ‖deriv (endpointCutoff ψ e n) x‖ ≤ (D + A * K) * endpointCutoffScale n := by
  have hAn : 0 ≤ A := (norm_nonneg (ψ x)).trans (hA x)
  have hDn : 0 ≤ D := (norm_nonneg (deriv ψ x)).trans (hD x)
  have hKn : 0 ≤ K := (norm_nonneg (deriv endpointCutoffBump x)).trans (hK x)
  have hBn : ‖endpointCutoffBump (endpointCutoffScale n * (x - e))‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg endpointCutoffBump.nonneg]
    exact endpointCutoffBump.le_one
  rw [endpointCutoff_deriv hψ]
  apply (norm_add_le _ _).trans
  have h₁ : ‖deriv ψ x * endpointCutoffBump (endpointCutoffScale n * (x - e))‖ ≤ D := by
    rw [norm_mul]
    exact (mul_le_mul (hD x) hBn (norm_nonneg _) hDn).trans_eq (mul_one D)
  have h₂ : ‖ψ x * deriv endpointCutoffBump (endpointCutoffScale n * (x - e)) * endpointCutoffScale n‖ ≤
      A * K * endpointCutoffScale n := by
    simp only [norm_mul, Real.norm_of_nonneg (endpointCutoffScale_pos n).le]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hA x) (hK _) (norm_nonneg _) hAn)
      (endpointCutoffScale_pos n).le
  have hDn' : D ≤ D * endpointCutoffScale n := le_mul_of_one_le_right hDn (endpointCutoffScale_one_le n)
  nlinarith only [h₁, h₂, hDn']

/-- Actual square-integral decay of the localized values. -/
theorem integral_sq_endpointCutoff_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {A : ℝ}
    (hA : ∀ x : ℝ, ‖ψ x‖ ≤ A) (e : ℝ) (n : ℕ) :
    (∫ x : ℝ, endpointCutoff ψ e n x ^ 2) ≤ (4 / endpointCutoffScale n) * A ^ 2 := by
  have hAn : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
  have hMem : MemLp (endpointCutoff ψ e n) 2 volume :=
    (endpointCutoff_contDiff hψ e n).continuous.memLp_of_hasCompactSupport
      (endpointCutoff_hasCompactSupport ψ e n)
  have hi := hMem.integrable_sq
  have h := integral_le_length_mul_of_support_bound hi
    (l := e - 2 / endpointCutoffScale n) (r := e + 2 / endpointCutoffScale n) (M := A ^ 2)
    (by have hrad : 0 ≤ 2 / endpointCutoffScale n := div_nonneg (by norm_num) (endpointCutoffScale_pos n).le; linarith)
    (fun x hx => by rw [endpointCutoff_zero_off ψ e n x hx]; norm_num)
    (fun x _ => by
      have hh := pow_le_pow_left₀ (norm_nonneg _) (endpointCutoff_norm_le hA e n x) 2
      simpa only [Real.norm_eq_abs, sq_abs] using hh)
  convert h using 1
  ring

private theorem integral_sq_endpointCutoff_deriv_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {A D K : ℝ} (hA : ∀ x : ℝ, ‖ψ x‖ ≤ A) (hD : ∀ x : ℝ, ‖deriv ψ x‖ ≤ D)
    (hK : ∀ x : ℝ, ‖deriv endpointCutoffBump x‖ ≤ K) (e : ℝ) (n : ℕ) :
    (∫ x : ℝ, deriv (endpointCutoff ψ e n) x ^ 2) ≤
      4 * (D + A * K) ^ 2 * endpointCutoffScale n := by
  have hdc := (endpointCutoff_contDiff hψ e n).continuous_deriv (by simp)
  have hMem : MemLp (deriv (endpointCutoff ψ e n)) 2 volume :=
    hdc.memLp_of_hasCompactSupport (endpointCutoff_hasCompactSupport ψ e n).deriv
  have hi := hMem.integrable_sq
  have h := integral_le_length_mul_of_support_bound hi
    (l := e - 2 / endpointCutoffScale n) (r := e + 2 / endpointCutoffScale n)
    (M := ((D + A * K) * endpointCutoffScale n) ^ 2)
    (by have hrad : 0 ≤ 2 / endpointCutoffScale n := div_nonneg (by norm_num) (endpointCutoffScale_pos n).le; linarith)
    (fun x hx => by rw [endpointCutoff_deriv_zero_off ψ e n x hx]; norm_num)
    (fun x _ => by
      have hh := pow_le_pow_left₀ (norm_nonneg _) (endpointCutoff_deriv_norm_le hψ hA hD hK e n x) 2
      simpa only [Real.norm_eq_abs, sq_abs] using hh)
  convert h using 1
  have hN : endpointCutoffScale n ≠ 0 := (endpointCutoffScale_pos n).ne'
  field_simp [hN]
  ring

/-- The actual Fourier half-energy of endpoint cutoffs is uniformly
bounded, independently of the center and localization scale. -/
theorem exists_endpointCutoff_energy_bound {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {A D : ℝ} (hA : ∀ x : ℝ, ‖ψ x‖ ≤ A) (hD : ∀ x : ℝ, ‖deriv ψ x‖ ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ e : ℝ, ∀ n : ℕ,
      energy (endpointCutoff ψ e n) (endpointCutoff ψ e n) ≤ B := by
  have hbSmooth : ContDiff ℝ ∞ endpointCutoffBump := endpointCutoffBump.contDiff
  have hbc : Continuous (deriv endpointCutoffBump) := hbSmooth.continuous_deriv (by simp)
  obtain ⟨K, hK⟩ := endpointCutoffBump.hasCompactSupport.deriv.exists_bound_of_continuous hbc
  have hAn : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
  have hDn : 0 ≤ D := (norm_nonneg (deriv ψ 0)).trans (hD 0)
  have hKn : 0 ≤ K := (norm_nonneg (deriv endpointCutoffBump 0)).trans (hK 0)
  let B : ℝ := 4 * A * (D + A * K)
  have hBn : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hBn, fun e n => ?_⟩
  have hNpos : 0 < endpointCutoffScale n := endpointCutoffScale_pos n
  have hV := integral_sq_endpointCutoff_le hψ hA e n
  have hDint := integral_sq_endpointCutoff_deriv_le hψ hA hD hK e n
  have hprod := mul_le_mul hV hDint
    (integral_nonneg fun x => sq_nonneg (deriv (endpointCutoff ψ e n) x))
    (show 0 ≤ (4 / endpointCutoffScale n) * A ^ 2 by positivity)
  have hid : ((4 / endpointCutoffScale n) * A ^ 2) *
      (4 * (D + A * K) ^ 2 * endpointCutoffScale n) = B ^ 2 := by
    dsimp only [B]
    field_simp [(endpointCutoffScale_pos n).ne']
    ring
  rw [hid] at hprod
  have hE := energy_sq_le_integral_sq_mul_integral_deriv_sq_of_compactSmooth
    (endpointCutoff_contDiff hψ e n) (endpointCutoff_hasCompactSupport ψ e n)
  nlinarith [energy_nonneg (endpointCutoff ψ e n)]

/-- The endpoint cutoff has vanishing pairing against every fixed actual
finite-energy function. No vanishing norm of the cutoff's own energy is
claimed or needed. -/
theorem energy_endpointCutoff_tendsto_zero {f ψ : ℝ → ℝ}
    (hf : Integrable f) (hef : FiniteEnergy f) (hψ : ContDiff ℝ ∞ ψ)
    {A D : ℝ} (hA : ∀ x : ℝ, ‖ψ x‖ ≤ A) (hD : ∀ x : ℝ, ‖deriv ψ x‖ ≤ D) (e : ℝ) :
    Tendsto (fun n => energy f (endpointCutoff ψ e n)) atTop (𝓝 0) := by
  obtain ⟨B, _, hB⟩ := exists_endpointCutoff_energy_bound hψ hA hD
  exact energy_tendsto_zero_of_integral_norm_tendsto_zero_of_bounded_energy hf hef
    (endpointCutoff_integrable hψ e) (endpointCutoff_finiteEnergy hψ e)
    (integral_norm_endpointCutoff_tendsto_zero hψ hA e) (hB e)

/-- Every fixed point different from the endpoint eventually lies beyond
the shrinking support. This is an exact eventual equality. -/
theorem endpointCutoff_eventually_eq_zero (ψ : ℝ → ℝ) (e : ℝ) {x : ℝ} (hx : x ≠ e) :
    ∀ᶠ n : ℕ in atTop, endpointCutoff ψ e n x = 0 := by
  have hlim : Tendsto (fun n : ℕ => 2 / endpointCutoffScale n) atTop (𝓝 0) := by
    simpa only [endpointCutoffScale, div_eq_mul_inv, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2
  have hd : 0 < |x - e| := abs_pos.mpr (sub_ne_zero.mpr hx)
  filter_upwards [hlim.eventually (eventually_lt_nhds hd)] with n hn
  exact endpointCutoff_eq_zero ψ e n hn.le

end Torsion.Spectral

module

public import Torsion.RestrictedSpectralParseval
public import Torsion.RestrictedSpectralIntervalHolder
public import Torsion.RestrictedSpectralPositivity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Small-support coercivity and the actual weak maximum principle

The exact source support length and actual Fourier Parseval identity give
a stronger coercivity constant on short intervals. Testing the original
form against the admitted positive part then proves a local weak maximum
principle, including a positive zeroth-order coefficient.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- The L¹ square bound with the actual length of any supporting interval. -/
theorem MemRestrictedFormDomain.integral_norm_sq_le_of_support_interval
    {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) {l r : ℝ} (hlr : l < r)
    (hzero : ∀ᵐ x : ℝ, x ∉ Icc l r → f x = 0) :
    (∫ x : ℝ, ‖f x‖) ^ 2 ≤ (r - l) * ∫ x : ℝ, f x ^ 2 := by
  have heq : (∫ x : ℝ, ‖f x‖) = ∫ x in l..r, ‖f x‖ := by
    rw [intervalIntegral.integral_of_le hlr.le, ← integral_Icc_eq_integral_Ioc]
    symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hzero] with x hx hout
    rw [hx hout, norm_zero]
  rw [heq]
  have h := hf.1.norm.intervalIntegral_sq_le l r
  simpa only [Real.norm_eq_abs, sq_abs, abs_of_pos (sub_pos.mpr hlr), mul_comm] using h

/-- An actual closed restricted form member supported on an interval of
length `r-l` has the quantitative coercivity constant `π/(4(r-l))`. -/
theorem MemRestrictedFormDomain.energy_ge_of_support_interval
    {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) {l r : ℝ} (hlr : l < r)
    (hzero : ∀ᵐ x : ℝ, x ∉ Icc l r → f x = 0) :
    (Real.pi / (4 * (r - l))) * (∫ x : ℝ, f x ^ 2) ≤ energy f f := by
  let M : ℝ := ∫ x : ℝ, f x ^ 2
  let L : ℝ := r - l
  let δ : ℝ := Real.pi / (2 * L)
  let W : ℝ → ℝ := fun ξ => |ξ| * ‖fourier f ξ‖ ^ 2
  let B : ℝ → ℝ := fun ξ =>
    (Icc (-δ) δ).indicator (fun _ : ℝ => L * M) ξ + (1 / δ) * W ξ
  have hL : 0 < L := sub_pos.mpr hlr
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hM : 0 ≤ M := integral_nonneg fun x => sq_nonneg _
  have hpointF (ξ : ℝ) : ‖fourier f ξ‖ ^ 2 ≤ L * M :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_fourier_le_integral_norm f ξ) 2).trans
      (hf.integral_norm_sq_le_of_support_interval hlr hzero)
  have hi : Integrable (fun ξ => ‖fourier f ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hf.fourier_parseval.1.aestronglyMeasurable).mp hf.fourier_parseval.1
  have he : Integrable W := hf.2.1
  have hbi : Integrable ((Icc (-δ) δ).indicator (fun _ : ℝ => L * M)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc
  have hb : Integrable B := hbi.add (he.const_mul (1 / δ))
  have hpoint (ξ : ℝ) : ‖fourier f ξ‖ ^ 2 ≤ B ξ := by
    by_cases hξ : ξ ∈ Icc (-δ) δ
    · simp only [B, indicator_of_mem hξ]
      exact (hpointF ξ).trans (le_add_of_nonneg_right (by dsimp only [W]; positivity))
    · have hξabs : δ ≤ |ξ| := le_of_not_ge (fun h => hξ (abs_le.1 h))
      simp only [B, indicator_of_notMem hξ, zero_add, W]
      have hfac : 1 ≤ (1 / δ) * |ξ| := by
        rw [one_div_mul_eq_div, le_div_iff₀ hδ]
        simpa only [one_mul] using hξabs
      nlinarith [mul_le_mul_of_nonneg_right hfac (sq_nonneg ‖fourier f ξ‖)]
  have hE : (∫ ξ : ℝ, W ξ) = (2 * Real.pi) * energy f f := by
    rw [energy_self]
    dsimp only [W]
    field_simp [Real.pi_ne_zero]
  have hB : (∫ ξ : ℝ, B ξ) = Real.pi * M + (2 * Real.pi / δ) * energy f f := by
    dsimp only [B]
    rw [integral_add hbi (he.const_mul _), integral_indicator measurableSet_Icc,
      setIntegral_const, Real.volume_real_Icc_of_le (by linarith : -δ ≤ δ),
      integral_const_mul, hE]
    simp only [smul_eq_mul]
    dsimp only [δ]
    field_simp [ne_of_gt hL, Real.pi_ne_zero]
    ring
  have hfull : (2 * Real.pi) * M ≤ Real.pi * M + (2 * Real.pi / δ) * energy f f := by
    simpa only [hf.fourier_parseval.2, hB] using integral_mono hi hb hpoint
  have hcoef : 2 * Real.pi / δ = 4 * L := by
    dsimp only [δ]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hcoef] at hfull
  change (Real.pi / (4 * L)) * M ≤ energy f f
  rw [div_mul_eq_mul_div, div_le_iff₀ (show 0 < 4 * L by positivity)]
  nlinarith only [hfull]

/-- Testing against the positive part controls its own actual energy. -/
theorem energy_pos_part_le_energy {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) :
    energy (fun x => Max.max (f x) 0) (fun x => Max.max (f x) 0) ≤
      energy f (fun x => Max.max (f x) 0) := by
  have h := energy_neg_part_le_neg_energy hf.neg
  simp only [neg_neg] at h
  have heq : (fun x => -f x) = fun x => (-1 : ℝ) * f x := by funext x; ring
  rw [heq, energy_const_mul_left] at h
  linarith

/-- The genuine weak maximum principle on a short supporting interval.
The positive-part test is admitted by the actual form's proved lattice
closure, rather than assumed as a new test space. -/
theorem MemRestrictedFormDomain.nonpos_of_small_support_subsolution
    {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) {l r a : ℝ} (hlr : l < r)
    (hsmall : a < Real.pi / (4 * (r - l)))
    (hzero : ∀ᵐ x : ℝ, x ∉ Icc l r → Max.max (f x) 0 = 0)
    (hweak : energy f (fun x => Max.max (f x) 0) ≤
      a * ∫ x : ℝ, (Max.max (f x) 0) ^ 2) :
    ∀ᵐ x : ℝ, f x ≤ 0 := by
  let p : ℝ → ℝ := fun x => Max.max (f x) 0
  have hp : MemRestrictedFormDomain p := hf.pos_part
  have hlow := hp.energy_ge_of_support_interval hlr hzero
  have hhigh := (energy_pos_part_le_energy hf).trans hweak
  have hM : 0 ≤ ∫ x : ℝ, p x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hMzero : (∫ x : ℝ, p x ^ 2) = 0 := by
    nlinarith only [hlow, hhigh, hsmall, hM]
  have hEzero : energy p p = 0 := by
    rw [hMzero, mul_zero] at hhigh
    exact le_antisymm hhigh (energy_nonneg _)
  have hz := (energy_eq_zero_iff hp.integrable hp.2.1).1 hEzero
  filter_upwards [hz] with x hx
  have hle := le_max_left (f x) 0
  change p x = 0 at hx
  rw [show Max.max (f x) 0 = p x from rfl, hx] at hle
  exact hle

end Torsion.Spectral

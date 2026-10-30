module

public import Torsion.RestrictedSpectralResolvent

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# From actual resolvent maximum bounds to restricted-form minimum bounds

The weak solution equation and Cauchy--Schwarz in the genuine frequency
Hilbert coordinate transfer a quadratic resolvent bound at a single source
into the reciprocal lower bound for the original restricted Fourier form.
This is the variational step needed to order the constructed eigenpairs.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral.RestrictedHilbert

/-- Cauchy--Schwarz for the actual source-normalized Fourier graph form. -/
theorem energy_cauchy_schwarz (p q : space) :
    (energy p q) ^ 2 ≤ energy p p * energy q q := by
  let c : ℝ := 1 / (2 * Real.pi)
  have h := real_inner_mul_inner_self_le (halfMap p) (halfMap q)
  calc
    (energy p q) ^ 2 = c ^ 2 *
        (inner (𝕜 := ℝ) (halfMap p) (halfMap q) *
          inner (𝕜 := ℝ) (halfMap p) (halfMap q)) := by
      rw [energy_apply]
      dsimp only [c]
      ring
    _ ≤ c ^ 2 * (inner (𝕜 := ℝ) (halfMap p) (halfMap p) *
        inner (𝕜 := ℝ) (halfMap q) (halfMap q)) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg c)
    _ = energy p p * energy q q := by
      simp only [energy_apply]
      dsimp only [c]
      ring

/-- The actual graph energy is nonnegative on its diagonal. -/
theorem energy_self_nonneg (q : space) : 0 ≤ energy q q := by
  rw [energy_apply, real_inner_self_eq_norm_sq]
  positivity

/-- A quadratic bound on the actual resolvent at the actual value source
of one graph element gives the reciprocal restricted-form lower bound. -/
theorem energy_ge_of_resolvent_quadratic_bound_at {μ : ℝ} (hμ : 0 < μ) (q : space)
    (hbound : inner (𝕜 := ℝ) (resolvent (valueMap q)) (valueMap q) ≤
      μ * ‖valueMap q‖ ^ 2) :
    (1 / μ) * ‖valueMap q‖ ^ 2 ≤ energy q q := by
  let f : ValueL2 := valueMap q
  let p : space := solutionOperator f
  have hpq : energy p q = ‖f‖ ^ 2 := by
    rw [energy_solutionOperator]
    exact real_inner_self_eq_norm_sq f
  have hpp : energy p p = inner (𝕜 := ℝ) (resolvent f) f := by
    rw [energy_solutionOperator, real_inner_comm]
    rfl
  have hcs := energy_cauchy_schwarz p q
  rw [hpq, hpp] at hcs
  have hm : (‖f‖ ^ 2) ^ 2 ≤ (μ * ‖f‖ ^ 2) * energy q q :=
    hcs.trans (mul_le_mul_of_nonneg_right hbound (energy_self_nonneg q))
  by_cases hf0 : f = 0
  · change (1 / μ) * ‖f‖ ^ 2 ≤ energy q q
    simp only [hf0, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    exact energy_self_nonneg q
  have hfpos : 0 < ‖f‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hf0)
  have hcancel : ‖f‖ ^ 2 ≤ μ * energy q q := by
    apply (mul_le_mul_iff_left₀ hfpos).mp
    convert hm using 1 <;> ring
  have hdiv : ‖f‖ ^ 2 / μ ≤ energy q q :=
    (div_le_iff₀ hμ).mpr (by simpa only [mul_comm] using hcancel)
  change (1 / μ) * ‖f‖ ^ 2 ≤ energy q q
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hdiv

end Torsion.Spectral.RestrictedHilbert

namespace Torsion.Spectral

/-- The resolvent maximum bound transfers to the original concrete
restricted Fourier integral and the original actual square integral. -/
theorem MemRestrictedFormDomain.energy_ge_of_resolvent_quadratic_bound_at
    {ψ : ℝ → ℝ} (hψ : MemRestrictedFormDomain ψ) {μ : ℝ} (hμ : 0 < μ)
    (hbound : inner (𝕜 := ℝ) (RestrictedHilbert.resolvent (hψ.1.toLp ψ)) (hψ.1.toLp ψ) ≤
      μ * ‖hψ.1.toLp ψ‖ ^ 2) :
    (1 / μ) * (∫ x : ℝ, (ψ x) ^ 2) ≤ energy ψ ψ := by
  have h := RestrictedHilbert.energy_ge_of_resolvent_quadratic_bound_at hμ
    (RestrictedHilbert.ofMemRestrictedFormDomain hψ) hbound
  simpa only [RestrictedHilbert.valueMap_ofMemRestrictedFormDomain,
    RestrictedHilbert.energy_ofMemRestrictedFormDomain,
    integral_sq_eq_norm_toLp_sq hψ.1] using h

end Torsion.Spectral

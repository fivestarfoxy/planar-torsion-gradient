import Torsion.Calibration
import Torsion.Stability

/-!
# Radial stability from a stationary calibration

This module combines the supporting-certificate and Hilbert-space modules.
It proves the implications (8.1), radial rigidity, and (8.2) directly from
stationary calibration and the Euler identity. `profileArea` is the Hilbert
model `‖R‖² / 2`; its identification with planar area and the construction
of the PDE calibration remain analytic inputs.
-/

noncomputable section

namespace Torsion.RadialStability

open Torsion.Calibration Torsion.Stability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Area-normalized marked flux in the Hilbert radial model. -/
def normalizedFlux (Q : E → ℝ) (r : E) : ℝ := Q r / Real.sqrt (profileArea r)

omit [InnerProductSpace ℝ E] in
/-- The stationary Euler identity makes the reference normalized flux positive. -/
theorem reference_flux_pos {Q : E → ℝ} {r₀ : E} {lam : ℝ}
    (h₀ : r₀ ≠ 0) (hlam : 0 < lam) (heuler : Q r₀ = lam * ‖r₀‖ ^ 2) :
    0 < normalizedFlux Q r₀ := by
  unfold normalizedFlux
  rw [reference_normalized_flux h₀ heuler]
  exact mul_pos (mul_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)) hlam)
    (norm_pos_iff.2 h₀)

/-- Theorem 8.1, (8.1), conditional on the stationary radial calibration.
No positivity hypothesis on `lam` is needed for this algebraic implication. -/
theorem quadratic_deficit {Q : E → ℝ} {r₀ r : E} {lam : ℝ}
    (h₀ : r₀ ≠ 0) (hr : r ≠ 0)
    (hcal : Q r ≤ lam * inner (𝕜 := ℝ) r₀ r)
    (heuler : Q r₀ = lam * ‖r₀‖ ^ 2) :
    normalizedFlux Q r₀ / 2 * ‖normalize r - normalize r₀‖ ^ 2 ≤
      normalizedFlux Q r₀ - normalizedFlux Q r := by
  have hc := normalized_inner_certificate h₀ hr hcal
  rw [← reference_normalized_flux h₀ heuler] at hc
  exact normalized_quadratic_deficit r r₀ hr h₀ hc

/-- Equality in the optimal normalized marked flux forces the competing
profile to be a positive multiple of the reference profile. -/
theorem rigidity {Q : E → ℝ} {r₀ r : E} {lam : ℝ}
    (h₀ : r₀ ≠ 0) (hr : r ≠ 0) (hlam : 0 < lam)
    (hcal : Q r ≤ lam * inner (𝕜 := ℝ) r₀ r)
    (heuler : Q r₀ = lam * ‖r₀‖ ^ 2)
    (hoptimal : normalizedFlux Q r = normalizedFlux Q r₀) :
    ∃ t : ℝ, 0 < t ∧ r = t • r₀ := by
  have hc := normalized_inner_certificate h₀ hr hcal
  rw [← reference_normalized_flux h₀ heuler] at hc
  change normalizedFlux Q r ≤ normalizedFlux Q r₀ *
    inner (𝕜 := ℝ) (normalize r) (normalize r₀) at hc
  rw [hoptimal] at hc
  exact normalized_rigidity r r₀ hr h₀ (reference_flux_pos h₀ hlam heuler) hc

/-- Theorem 8.1, (8.2): at area one the unnormalized `L²` deficit has
coefficient one fourth of the optimal marked flux. -/
theorem area_one_deficit {Q : E → ℝ} {r₀ r : E} {lam : ℝ}
    (hA₀ : profileArea r₀ = 1) (hA : profileArea r = 1)
    (hcal : Q r ≤ lam * inner (𝕜 := ℝ) r₀ r)
    (heuler : Q r₀ = lam * ‖r₀‖ ^ 2) :
    Q r₀ / 4 * ‖r - r₀‖ ^ 2 ≤ Q r₀ - Q r := by
  have hn₀ : ‖r₀‖ ^ 2 = 2 := by unfold profileArea at hA₀; linarith
  have hn : ‖r‖ ^ 2 = 2 := by unfold profileArea at hA; linarith
  apply area_one_quadratic_deficit r r₀ hn hn₀
  calc
    Q r ≤ lam * inner (𝕜 := ℝ) r₀ r := hcal
    _ = Q r₀ / 2 * inner (𝕜 := ℝ) r r₀ := by
      rw [heuler, hn₀, real_inner_comm r r₀]
      ring

/-- At fixed area one, equality determines the profile itself. -/
theorem area_one_rigidity {Q : E → ℝ} {r₀ r : E} {lam : ℝ}
    (hA₀ : profileArea r₀ = 1) (hA : profileArea r = 1) (hlam : 0 < lam)
    (hcal : Q r ≤ lam * inner (𝕜 := ℝ) r₀ r)
    (heuler : Q r₀ = lam * ‖r₀‖ ^ 2) (hoptimal : Q r = Q r₀) : r = r₀ := by
  have hd := area_one_deficit hA₀ hA hcal heuler
  rw [hoptimal, sub_self] at hd
  have hn₀ : ‖r₀‖ ^ 2 = 2 := by unfold profileArea at hA₀; linarith
  have hc : 0 < Q r₀ / 4 := by rw [heuler, hn₀]; positivity
  have hnormsq : ‖r - r₀‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hd hc
  have hz : ‖r - r₀‖ = 0 := sq_eq_zero_iff.mp (le_antisymm hnormsq (sq_nonneg _))
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end Torsion.RadialStability

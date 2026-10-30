module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Hilbert-space rigidity and quantitative stability

This file formalizes the Hilbert-space part of Theorem 8.1 of the writeup.
The PDE calibration inequality is an explicit hypothesis, not an axiom.
The space `E` can in particular be the real space `L²(0, π)`.
-/

namespace Torsion.Stability

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The elementary identity used for unit radial profiles in (8.1). -/
theorem unit_inner_deficit (r r₀ : E) (hr : ‖r‖ = 1) (hr₀ : ‖r₀‖ = 1) :
    1 - inner (𝕜 := ℝ) r r₀ = ‖r - r₀‖ ^ 2 / 2 := by
  have h := norm_sub_sq_real r r₀
  rw [hr, hr₀] at h
  nlinarith

/-- A calibration against a unit reference gives the quadratic deficit (8.1). -/
theorem unit_quadratic_deficit (r r₀ : E) (hr : ‖r‖ = 1) (hr₀ : ‖r₀‖ = 1)
    {c J : ℝ} (hcal : J ≤ c * inner (𝕜 := ℝ) r r₀) :
    c / 2 * ‖r - r₀‖ ^ 2 ≤ c - J := by
  have h := unit_inner_deficit r r₀ hr hr₀
  have hid : c / 2 * ‖r - r₀‖ ^ 2 = c - c * inner (𝕜 := ℝ) r r₀ := by
    calc
      c / 2 * ‖r - r₀‖ ^ 2 = c * (‖r - r₀‖ ^ 2 / 2) := by ring
      _ = c * (1 - inner (𝕜 := ℝ) r r₀) := by rw [← h]
      _ = c - c * inner (𝕜 := ℝ) r r₀ := by ring
  rw [hid]
  linarith

/-- Equality with a positive calibrated optimum forces equality of unit profiles. -/
theorem unit_rigidity (r r₀ : E) (hr : ‖r‖ = 1) (hr₀ : ‖r₀‖ = 1)
    {c : ℝ} (hc : 0 < c) (hcal : c ≤ c * inner (𝕜 := ℝ) r r₀) : r = r₀ := by
  have h := unit_quadratic_deficit r r₀ hr hr₀ hcal
  have hs : ‖r - r₀‖ ^ 2 = 0 := by
    have hnonpos : c / 2 * ‖r - r₀‖ ^ 2 ≤ 0 := by simpa using h
    have hsle : ‖r - r₀‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hnonpos (by linarith : 0 < c / 2)
    exact le_antisymm hsle (sq_nonneg _)
  have hn : ‖r - r₀‖ = 0 := (sq_eq_zero_iff).mp hs
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Normalization of a nonzero profile to the unit sphere. -/
def normalize (x : E) : E := ‖x‖⁻¹ • x

/-- A nonzero profile has unit norm after normalization. -/
theorem norm_normalize (x : E) (hx : x ≠ 0) : ‖normalize x‖ = 1 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp [normalize, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    inv_mul_cancel₀ hn]

/-- Recovering a profile from its normalization. -/
theorem norm_smul_normalize (x : E) : ‖x‖ • normalize x = x := by
  by_cases hx : x = 0
  · simp [hx, normalize]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    simp [normalize, smul_smul, mul_inv_cancel₀ hn]

/-- The quantitative estimate for arbitrary nonzero radial profiles. -/
theorem normalized_quadratic_deficit (R R₀ : E) (hR : R ≠ 0) (hR₀ : R₀ ≠ 0)
    {c J : ℝ} (hcal : J ≤ c * inner (𝕜 := ℝ) (normalize R) (normalize R₀)) :
    c / 2 * ‖normalize R - normalize R₀‖ ^ 2 ≤ c - J :=
  unit_quadratic_deficit _ _ (norm_normalize R hR) (norm_normalize R₀ hR₀) hcal

/-- Equality of normalized nonzero profiles is precisely positive proportionality. -/
theorem positive_multiple_of_normalize_eq (R R₀ : E) (hR : R ≠ 0) (hR₀ : R₀ ≠ 0)
    (heq : normalize R = normalize R₀) : ∃ t : ℝ, 0 < t ∧ R = t • R₀ := by
  refine ⟨‖R‖ / ‖R₀‖, div_pos (norm_pos_iff.mpr hR) (norm_pos_iff.mpr hR₀), ?_⟩
  calc
    R = ‖R‖ • normalize R := (norm_smul_normalize R).symm
    _ = ‖R‖ • normalize R₀ := by rw [heq]
    _ = (‖R‖ / ‖R₀‖) • R₀ := by simp [normalize, smul_smul, div_eq_mul_inv]

/-- The equality conclusion in Theorem 8.1, conditional on calibration. -/
theorem normalized_rigidity (R R₀ : E) (hR : R ≠ 0) (hR₀ : R₀ ≠ 0)
    {c : ℝ} (hc : 0 < c)
    (hcal : c ≤ c * inner (𝕜 := ℝ) (normalize R) (normalize R₀)) :
    ∃ t : ℝ, 0 < t ∧ R = t • R₀ := by
  apply positive_multiple_of_normalize_eq R R₀ hR hR₀
  exact unit_rigidity _ _ (norm_normalize R hR) (norm_normalize R₀ hR₀) hc hcal

/-- For area-one profiles, both squared `L²` norms equal two. This gives (8.2). -/
theorem area_one_quadratic_deficit (R R₀ : E)
    (hR : ‖R‖ ^ 2 = 2) (hR₀ : ‖R₀‖ ^ 2 = 2)
    {c J : ℝ} (hcal : J ≤ c / 2 * inner (𝕜 := ℝ) R R₀) :
    c / 4 * ‖R - R₀‖ ^ 2 ≤ c - J := by
  have h := norm_sub_sq_real R R₀
  rw [hR, hR₀] at h
  have hi : inner (𝕜 := ℝ) R R₀ = 2 - ‖R - R₀‖ ^ 2 / 2 := by linarith
  rw [hi] at hcal
  nlinarith

end

end Torsion.Stability

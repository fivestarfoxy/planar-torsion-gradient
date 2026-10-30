import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The supporting-functional part of radial calibration

This file proves the functional-analytic implications in Theorem 4.2 of the
writeup. The PDE identification of the derivative, radial concavity, and the
existence/convergence of endpoint cutoffs are **hypotheses**, not asserted
analytic theorems. In particular no domain, torsion function or spectral
eigenfunction is constructed in this file.
-/

noncomputable section

namespace Torsion.Calibration

open Set Filter
open scoped Topology

section SupportingFunctional

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {C : Set E} {Q : E → ℝ} {r₀ r : E} {d : ℝ}

/-- A right derivative of a concave functional bounds its secant slope. The
derivative is only along the segment from the reference to the competitor. -/
theorem tangent_bound
    (hQ : ConcaveOn ℝ C Q) (h₀ : r₀ ∈ C) (hr : r ∈ C)
    (hd : HasDerivWithinAt (fun t : ℝ => Q (AffineMap.lineMap r₀ r t))
      d (Ioi 0) 0) :
    Q r ≤ Q r₀ + d := by
  have h := (hQ.comp_affineMap (AffineMap.lineMap r₀ r)).slope_le_of_hasDerivWithinAt_Ioi
    (by simpa using h₀) (by simpa using hr) (by norm_num : (0 : ℝ) < 1) hd
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at h
  linarith

/-- The Euler identity cancels the affine intercept in the tangent bound. -/
theorem euler_calibration
    (L : E →ₗ[ℝ] ℝ) (hQ : ConcaveOn ℝ C Q) (h₀ : r₀ ∈ C) (hr : r ∈ C)
    (hd : HasDerivWithinAt (fun t : ℝ => Q (AffineMap.lineMap r₀ r t))
      (L (r - r₀)) (Ioi 0) 0)
    (heuler : Q r₀ = L r₀) :
    Q r ≤ L r := by
  have h := tangent_bound hQ h₀ hr hd
  rw [heuler, map_sub] at h
  linarith

end SupportingFunctional

/-- The minimum cutoff used at the endpoints is increasing as the cutoff
coefficient increases. The sign of the perturbation `b - a` is unrestricted. -/
theorem lower_cutoff_mono {a b χ ψ : ℝ}
    (hχ : χ ≤ 1) (hψ : ψ ≤ 1) (hχψ : χ ≤ ψ) :
    min b (a + χ * (b - a)) ≤ min b (a + ψ * (b - a)) := by
  by_cases hab : a ≤ b
  · apply min_le_min le_rfl
    nlinarith
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    have hleft : b ≤ a + χ * (b - a) := by nlinarith
    have hright : b ≤ a + ψ * (b - a) := by nlinarith
    rw [min_eq_left hleft, min_eq_left hright]

/-- Positive endpoint radii remain positive under a cutoff convex combination. -/
theorem cutoff_positive {a b χ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hχ₀ : 0 ≤ χ) (hχ₁ : χ ≤ 1) :
    0 < a + χ * (b - a) := by
  by_cases hab : a ≤ b
  · have : 0 ≤ χ * (b - a) := mul_nonneg hχ₀ (sub_nonneg.2 hab)
    linarith
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    have : b ≤ a + χ * (b - a) := by nlinarith
    linarith

/-- Pointwise convergence of the lower cutoff requires only convergence of
the scalar cutoff coefficient. -/
theorem lower_cutoff_tendsto {a b : ℝ} {χ : ℕ → ℝ}
    (hχ : Tendsto χ atTop (𝓝 1)) :
    Tendsto (fun n => min b (a + χ n * (b - a))) atTop (𝓝 b) := by
  have h : Tendsto (fun n => min b (a + χ n * (b - a))) atTop
      (𝓝 (min b (a + 1 * (b - a)))) :=
    tendsto_const_nhds.min (tendsto_const_nhds.add (hχ.mul_const (b - a)))
  simpa [show a + (1 : ℝ) * (b - a) = b by ring] using h

/-- Endpoint passage in the calibration proof. The lower cutoffs converge in
flux and lie below the compact-perturbation competitors. Only the linear
functional must converge on the latter; their fluxes need not converge.

For the writeup take `lower n = min R (R₀ + χₙ (R - R₀))` and
`competitor n = R₀ + χₙ (R - R₀)`. Their construction and analytic convergence
remain separate obligations. -/
theorem calibration_of_cutoff
    {P : Type*} (Q L : P → ℝ) (r : P) (lower competitor : ℕ → P)
    (hbelow : ∀ n, Q (lower n) ≤ Q (competitor n))
    (hcompact : ∀ n, Q (competitor n) ≤ L (competitor n))
    (hflux : Tendsto (fun n => Q (lower n)) atTop (𝓝 (Q r)))
    (hlinear : Tendsto (fun n => L (competitor n)) atTop (𝓝 (L r))) :
    Q r ≤ L r := by
  exact le_of_tendsto_of_tendsto' hflux hlinear fun n => (hbelow n).trans (hcompact n)

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Cauchy--Schwarz step of Theorem 4.2. -/
theorem calibration_norm_bound {Q : E → ℝ} {γ r : E}
    (hcal : Q r ≤ inner (𝕜 := ℝ) γ r) :
    Q r ≤ ‖γ‖ * ‖r‖ :=
  hcal.trans (real_inner_le_norm γ r)

/-- Squared profile norm is twice radial area. This is a Hilbert-space model
of the polar-coordinate formula; it does not assert that formula for domains. -/
def profileArea (r : E) : ℝ := ‖r‖ ^ 2 / 2

omit [InnerProductSpace ℝ E] in
theorem profileArea_pos {r : E} (hr : r ≠ 0) : 0 < profileArea r := by
  unfold profileArea
  exact div_pos (sq_pos_of_pos (norm_pos_iff.2 hr)) (by norm_num)

omit [InnerProductSpace ℝ E] in
/-- Exact conversion between the radial area normalization and the Hilbert
norm normalization. -/
theorem norm_eq_sqrt_two_mul_sqrt_profileArea (r : E) :
    ‖r‖ = Real.sqrt 2 * Real.sqrt (profileArea r) := by
  have hA : 0 ≤ profileArea r := by unfold profileArea; positivity
  have hsqA := Real.sq_sqrt hA
  have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hnonneg : 0 ≤ Real.sqrt 2 * Real.sqrt (profileArea r) := by positivity
  have hn := norm_nonneg r
  have hprod : (Real.sqrt 2 * Real.sqrt (profileArea r)) ^ 2 = ‖r‖ ^ 2 := by
    rw [mul_pow, hsq2, hsqA]
    unfold profileArea
    ring
  exact (sq_eq_sq₀ hn hnonneg).1 hprod.symm

/-- The area-normalized upper bound `√2 ‖γ‖` from a supporting certificate. -/
theorem normalized_calibration_bound {Q : E → ℝ} {γ r : E}
    (hr : r ≠ 0) (hcal : Q r ≤ inner (𝕜 := ℝ) γ r) :
    Q r / Real.sqrt (profileArea r) ≤ Real.sqrt 2 * ‖γ‖ := by
  have hs : 0 < Real.sqrt (profileArea r) := Real.sqrt_pos.2 (profileArea_pos hr)
  apply (div_le_iff₀ hs).2
  have h := calibration_norm_bound hcal
  rw [norm_eq_sqrt_two_mul_sqrt_profileArea r] at h
  nlinarith

omit [InnerProductSpace ℝ E] in
/-- The reference Euler identity computes its normalized marked flux. -/
theorem reference_normalized_flux {Q : E → ℝ} {r₀ : E} {lam : ℝ}
    (h₀ : r₀ ≠ 0) (heuler : Q r₀ = lam * ‖r₀‖ ^ 2) :
    Q r₀ / Real.sqrt (profileArea r₀) = Real.sqrt 2 * lam * ‖r₀‖ := by
  have hs : Real.sqrt (profileArea r₀) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (profileArea_pos h₀))
  apply (div_eq_iff hs).2
  rw [heuler]
  calc
    lam * ‖r₀‖ ^ 2 = lam * ‖r₀‖ * (Real.sqrt 2 * Real.sqrt (profileArea r₀)) := by
      rw [← norm_eq_sqrt_two_mul_sqrt_profileArea r₀]
      ring
    _ = (Real.sqrt 2 * lam * ‖r₀‖) * Real.sqrt (profileArea r₀) := by ring

/-- The calibrated upper bound retains the angle between normalized profiles.
This is the input to the Hilbert-space stability identity in Section 8. -/
theorem normalized_inner_certificate {Q : E → ℝ} {r₀ r : E} {lam : ℝ}
    (h₀ : r₀ ≠ 0) (hr : r ≠ 0) (hcal : Q r ≤ lam * inner (𝕜 := ℝ) r₀ r) :
    Q r / Real.sqrt (profileArea r) ≤
      (Real.sqrt 2 * lam * ‖r₀‖) *
        inner (𝕜 := ℝ) (‖r‖⁻¹ • r) (‖r₀‖⁻¹ • r₀) := by
  have hs : 0 < Real.sqrt (profileArea r) := Real.sqrt_pos.2 (profileArea_pos hr)
  have hn : ‖r‖ ≠ 0 := norm_ne_zero_iff.2 hr
  have hn₀ : ‖r₀‖ ≠ 0 := norm_ne_zero_iff.2 h₀
  apply (div_le_div_of_nonneg_right hcal hs.le).trans
  apply le_of_eq
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm r r₀]
  field_simp [hn, hn₀, ne_of_gt hs]
  rw [norm_eq_sqrt_two_mul_sqrt_profileArea r]
  ring

/-- Stationarity (`γ = lam r₀`) and the Euler identity give global optimality
in the radial Hilbert model, as in Corollary 4.5. -/
theorem stationary_normalized_bound {Q : E → ℝ} {r₀ r : E} {lam : ℝ}
    (hlam : 0 ≤ lam) (h₀ : r₀ ≠ 0) (hr : r ≠ 0)
    (hcal : Q r ≤ lam * inner (𝕜 := ℝ) r₀ r)
    (heuler : Q r₀ = lam * ‖r₀‖ ^ 2) :
    Q r / Real.sqrt (profileArea r) ≤ Q r₀ / Real.sqrt (profileArea r₀) := by
  have hc : Q r ≤ inner (𝕜 := ℝ) (lam • r₀) r := by
    simpa only [real_inner_smul_left] using hcal
  have hb := normalized_calibration_bound hr hc
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam] at hb
  rw [reference_normalized_flux h₀ heuler]
  nlinarith

end Hilbert

end Torsion.Calibration

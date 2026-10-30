module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Smooth endpoint cutoffs with explicit radii and derivative. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace Torsion.Spectral

/-- Fixed smooth plateau: one on the unit interval and zero beyond radius two. -/
def endpointCutoffBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The endpoint localization scale. -/
def endpointCutoffScale (n : ℕ) : ℝ := (n : ℝ) + 1

theorem endpointCutoffScale_one_le (n : ℕ) : 1 ≤ endpointCutoffScale n := by
  unfold endpointCutoffScale
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem endpointCutoffScale_pos (n : ℕ) : 0 < endpointCutoffScale n :=
  lt_of_lt_of_le zero_lt_one (endpointCutoffScale_one_le n)

/-- The actual smooth part of a test function localized at the endpoint `e`. -/
def endpointCutoff (ψ : ℝ → ℝ) (e : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ψ x * endpointCutoffBump (endpointCutoffScale n * (x - e))

/-- Vanishing beyond the explicit outer cutoff radius. -/
theorem endpointCutoff_eq_zero (ψ : ℝ → ℝ) (e : ℝ) (n : ℕ) {x : ℝ}
    (hx : 2 / endpointCutoffScale n ≤ |x - e|) : endpointCutoff ψ e n x = 0 := by
  have hdist : (endpointCutoffBump).rOut ≤ dist (endpointCutoffScale n * (x - e)) 0 := by
    change 2 ≤ dist (endpointCutoffScale n * (x - e)) 0
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (endpointCutoffScale_pos n)]
    have h := (div_le_iff₀ (endpointCutoffScale_pos n)).mp hx
    nlinarith
  simp only [endpointCutoff, endpointCutoffBump.zero_of_le_dist hdist, mul_zero]

/-- Agreement with the test function throughout the inner plateau. -/
theorem endpointCutoff_eq_self (ψ : ℝ → ℝ) (e : ℝ) (n : ℕ) {x : ℝ}
    (hx : |x - e| ≤ 1 / endpointCutoffScale n) : endpointCutoff ψ e n x = ψ x := by
  have hdist : endpointCutoffScale n * (x - e) ∈ closedBall (0 : ℝ) endpointCutoffBump.rIn := by
    change dist (endpointCutoffScale n * (x - e)) 0 ≤ 1
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (endpointCutoffScale_pos n)]
    have h := (le_div_iff₀ (endpointCutoffScale_pos n)).mp hx
    nlinarith
  simp only [endpointCutoff, endpointCutoffBump.one_of_mem_closedBall hdist, mul_one]

/-- The topological support is confined to the explicit shrinking interval. -/
theorem endpointCutoff_tsupport_subset (ψ : ℝ → ℝ) (e : ℝ) (n : ℕ) :
    tsupport (endpointCutoff ψ e n) ⊆
      Icc (e - 2 / endpointCutoffScale n) (e + 2 / endpointCutoffScale n) := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra hxi
  have habs : 2 / endpointCutoffScale n ≤ |x - e| := by
    by_contra ha
    have hlt : |x - e| < 2 / endpointCutoffScale n := lt_of_not_ge ha
    have h := abs_lt.mp hlt
    exact hxi ⟨by linarith [h.1], by linarith [h.2]⟩
  exact hx (endpointCutoff_eq_zero ψ e n habs)

/-- Compact support does not require any regularity of the original test function. -/
theorem endpointCutoff_hasCompactSupport (ψ : ℝ → ℝ) (e : ℝ) (n : ℕ) :
    HasCompactSupport (endpointCutoff ψ e n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (endpointCutoff_tsupport_subset ψ e n)

/-- A smooth datum gives a smooth localized cutoff. -/
theorem endpointCutoff_contDiff {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (e : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (endpointCutoff ψ e n) :=
  hψ.mul (endpointCutoffBump.contDiff.comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const)))

/-- Exact derivative of the localized cutoff, with its explicit scale factor. -/
theorem endpointCutoff_deriv {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (e : ℝ) (n : ℕ) (x : ℝ) :
    deriv (endpointCutoff ψ e n) x =
      deriv ψ x * endpointCutoffBump (endpointCutoffScale n * (x - e)) +
        ψ x * deriv endpointCutoffBump (endpointCutoffScale n * (x - e)) * endpointCutoffScale n := by
  have hinner : HasDerivAt (fun x : ℝ => endpointCutoffScale n * (x - e)) (endpointCutoffScale n) x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).sub_const e).const_mul (endpointCutoffScale n)
  have hb : HasDerivAt endpointCutoffBump
      (deriv endpointCutoffBump (endpointCutoffScale n * (x - e)))
      (endpointCutoffScale n * (x - e)) :=
    ((endpointCutoffBump.contDiff : ContDiff ℝ ∞ endpointCutoffBump).differentiable (by simp) _).hasDerivAt
  have hp : HasDerivAt ψ (deriv ψ x) x := (hψ.differentiable (by simp) x).hasDerivAt
  have h := (hp.mul (hb.comp x hinner)).deriv
  simpa only [endpointCutoff, mul_assoc, Pi.mul_apply, Function.comp_apply] using! h

end Torsion.Spectral

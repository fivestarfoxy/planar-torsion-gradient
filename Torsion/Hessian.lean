import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The finite-dimensional Hessian identity

This file proves the algebraic core of Lemma 3.4, equation (3.3), of
`torsion-full-writeup.pdf`. It does not assume differentiability: the matrix
hypotheses are precisely symmetry, a positive null vector, and nonnegative
entries away from the diagonal. Deriving these hypotheses from Euler's identity
and supermodularity, and the analytic smoothing passage, are separate tasks.
-/

namespace Torsion
namespace Hessian

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- A symmetric matrix whose row sums vanish has the usual graph-Laplacian
quadratic-form identity. No sign assumptions enter this identity. -/
theorem row_sum_identity (K : ι → ι → ℝ)
    (hsymm : ∀ i j, K i j = K j i)
    (hrows : ∀ i, ∑ j, K i j = 0) (w : ι → ℝ) :
    (∑ i, ∑ j, K i j * w i * w j) =
      -(1 / 2 : ℝ) * (∑ i, ∑ j, K i j * (w i - w j) ^ 2) := by
  classical
  have hleft : (∑ i, ∑ j, K i j * (w i) ^ 2) = 0 := by
    simp_rw [← Finset.sum_mul, hrows]
    simp
  have hright : (∑ i, ∑ j, K i j * (w j) ^ 2) = 0 := by
    calc
      _ = ∑ j, ∑ i, K i j * (w j) ^ 2 := Finset.sum_comm
      _ = ∑ j, ∑ i, K j i * (w j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsymm i j]
      _ = 0 := by
        simp_rw [← Finset.sum_mul, hrows]
        simp
  have hexpand : (∑ i, ∑ j, K i j * (w i - w j) ^ 2) =
      (∑ i, ∑ j, K i j * (w i) ^ 2) +
      (∑ i, ∑ j, K i j * (w j) ^ 2) -
      2 * (∑ i, ∑ j, K i j * w i * w j) := by
    calc
      _ = ∑ i, ∑ j, (K i j * (w i) ^ 2 + K i j * (w j) ^ 2 -
          2 * (K i j * w i * w j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
  rw [hleft, hright] at hexpand
  linarith

/-- The symmetric positive-null-vector form of equation (3.3), written as a
sum over all ordered pairs. Each unordered pair is therefore counted twice. -/
theorem weighted_identity (H : ι → ι → ℝ) (x : ι → ℝ)
    (hsymm : ∀ i j, H i j = H j i)
    (hnull : ∀ i, ∑ j, H i j * x j = 0) (w : ι → ℝ) :
    (∑ i, ∑ j, H i j * x i * x j * w i * w j) =
      -(1 / 2 : ℝ) *
        (∑ i, ∑ j, H i j * x i * x j * (w i - w j) ^ 2) := by
  classical
  apply row_sum_identity (fun i j => H i j * x i * x j)
  · intro i j
    rw [hsymm i j]
    ring
  · intro i
    calc
      _ = x i * ∑ j, H i j * x j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hnull i, mul_zero]

/-- Nonnegative off-diagonal entries and a positive null vector force the
matrix to be negative semidefinite. This is the algebraic step in the smooth
case of Lemma 3.4. -/
theorem quadratic_form_nonpos (H : ι → ι → ℝ) (x : ι → ℝ)
    (hsymm : ∀ i j, H i j = H j i)
    (hx : ∀ i, 0 < x i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ H i j)
    (hnull : ∀ i, ∑ j, H i j * x j = 0) (v : ι → ℝ) :
    (∑ i, ∑ j, v i * H i j * v j) ≤ 0 := by
  classical
  have hnonneg : 0 ≤ ∑ i, ∑ j,
      H i j * x i * x j * (v i / x i - v j / x j) ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    by_cases hij : i = j
    · subst j
      simp
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (hoff i j hij) (le_of_lt (hx i)))
          (le_of_lt (hx j))) (sq_nonneg _)
  have hidentity := weighted_identity H x hsymm hnull (fun i => v i / x i)
  have hleft : (∑ i, ∑ j, H i j * x i * x j * (v i / x i) * (v j / x j)) =
      ∑ i, ∑ j, v i * H i j * v j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [ne_of_gt (hx i), ne_of_gt (hx j)]
    ring
  rw [hleft] at hidentity
  linarith

end Hessian
end Torsion

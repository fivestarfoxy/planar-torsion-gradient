module

public import Torsion.CauchyTransformMoments
public import Torsion.Moments
public import Mathlib.Tactic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The concrete spectral moment identity from the holomorphic identity

This module derives `a * N = 2 * b * M` for the actual integrals of the
spectral construction, using their proved asymptotic limits along the positive
imaginary axis. The quadratic holomorphic identity remains an explicit
hypothesis; deriving it from the spectral boundary equation is a separate
complex-analytic obligation. No relation between the moments is assumed here.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace Torsion.Spectral

private def imaginaryRay (n : ℕ) : ℂ := (((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I

private theorem imaginaryRay_mem (n : ℕ) : imaginaryRay n ∈ upperHalfPlane := by
  change 0 < (imaginaryRay n).im
  simp [imaginaryRay]
  positivity

private theorem imaginaryRay_norm_tendsto :
    Tendsto (fun n => ‖imaginaryRay n‖) atTop atTop := by
  have hn (n : ℕ) : ‖imaginaryRay n‖ = (n : ℝ) + 1 := by
    unfold imaginaryRay
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)]
  simp_rw [hn]
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

/-- Comparing the proved derivative moments at infinity in the concrete
quadratic holomorphic identity gives the moment relation (5.4). -/
theorem moment_identity_of_quadratic_identity {a b : ℝ} {φ : ℝ → ℝ}
    (ha : a ≠ 0) (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hidentity : ∀ z ∈ upperHalfPlane,
      deriv (auxiliary φ) z = ((b / a : ℝ) : ℂ) * deriv (cauchy φ) z -
        (deriv (cauchy φ) z) ^ 2 / ((2 * a : ℝ) : ℂ)) :
    a * squareMass φ = 2 * b * mass φ := by
  have hH : ∀ᶠ n : ℕ in atTop, imaginaryRay n ∈ upperHalfPlane :=
    Eventually.of_forall imaginaryRay_mem
  have hF := cauchy_derivative_moment hφ imaginaryRay_norm_tendsto hH
  have hF0 := cauchy_derivative_tendsto_zero hφ imaginaryRay_norm_tendsto hH
  have hA := auxiliary_derivative_moment hφ imaginaryRay_norm_tendsto hH
  have hF2 : Tendsto (fun n => (imaginaryRay n) ^ 2 *
      (deriv (cauchy φ) (imaginaryRay n)) ^ 2) atTop (𝓝 0) := by
    have hh := hF.mul hF0
    simp only [mul_zero] at hh
    convert hh using 1
    funext n
    ring
  have hR := (hF.const_mul ((b / a : ℝ) : ℂ)).sub
    (hF2.div_const ((2 * a : ℝ) : ℂ))
  simp only [zero_div, sub_zero] at hR
  have hA' : Tendsto (fun n => (imaginaryRay n) ^ 2 *
      deriv (auxiliary φ) (imaginaryRay n)) atTop
      (𝓝 (((b / a : ℝ) : ℂ) * ((Real.pi : ℂ)⁻¹ * (mass φ : ℂ)))) := by
    apply hR.congr'
    filter_upwards [] with n
    rw [hidentity (imaginaryRay n) (imaginaryRay_mem n)]
    ring
  have heq := tendsto_nhds_unique hA hA'
  have hreal : (2 * Real.pi)⁻¹ * squareMass φ =
      (b / a) * (Real.pi⁻¹ * mass φ) := by
    exact_mod_cast heq
  field_simp [ha, Real.pi_ne_zero] at hreal
  nlinarith [hreal]

/-- Positivity of the linear coefficient `b` follows from the concrete moment
identity and positive spectral moments, rather than being another input. -/
theorem coefficient_pos_of_quadratic_identity {a b : ℝ} {φ : ℝ → ℝ}
    (ha : 0 < a) (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hM : 0 < mass φ) (hN : 0 < squareMass φ)
    (hidentity : ∀ z ∈ upperHalfPlane,
      deriv (auxiliary φ) z = ((b / a : ℝ) : ℂ) * deriv (cauchy φ) z -
        (deriv (cauchy φ) z) ^ 2 / ((2 * a : ℝ) : ℂ)) :
    0 < b := by
  have hm := moment_identity_of_quadratic_identity ha.ne' hφ hidentity
  have hb : b = a * squareMass φ / (2 * mass φ) := by
    apply (eq_div_iff (by positivity : 2 * mass φ ≠ 0)).2
    nlinarith [hm]
  rw [hb]
  positivity

/-- The concrete Cauchy construction supplies abstract moment data once its
quadratic holomorphic identity and positive input data have been proved. -/
def momentsOfQuadraticIdentity {a b : ℝ} {φ : ℝ → ℝ}
    (ha : 0 < a) (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hidentity : ∀ z ∈ upperHalfPlane,
      deriv (auxiliary φ) z = ((b / a : ℝ) : ℂ) * deriv (cauchy φ) z -
        (deriv (cauchy φ) z) ^ 2 / ((2 * a : ℝ) : ℂ)) : Torsion.Moments where
  a := a
  b := b
  M := mass φ
  N := squareMass φ
  a_pos := ha
  b_pos := coefficient_pos_of_quadratic_identity ha hφ
    (mass_pos hφ hpos) (squareMass_pos hφ hpos) hidentity
  M_pos := mass_pos hφ hpos
  N_pos := squareMass_pos hφ hpos
  moment := moment_identity_of_quadratic_identity ha.ne' hφ hidentity

end Torsion.Spectral

end

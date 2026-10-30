import Torsion.CauchyTransformUniqueness
import Torsion.SpectralMomentIdentity
import Torsion.ComplexIdentity

/-!
# The quadratic Cauchy identity from the linear boundary equation

The boundedness required by holomorphic uniqueness is derived here from
continuity on the closed half-plane and the actual Cauchy-kernel bounds at
infinity.  The remaining inputs are the boundary extensions and their traces,
including the linear spectral boundary equation; the quadratic identity is
not an input.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace Torsion.Spectral

/-- Continuity on the closed half-plane and a bound outside a fixed ball
give a global interior bound.  The compact part of the domain is bounded by
continuity, so no global boundedness hypothesis is needed. -/
theorem bounded_on_upperHalfPlane_of_continuousOn_closure
    {f : ℂ → ℂ} (hf : ContinuousOn f (closure upperHalfPlane))
    (C : ℝ) (hC : ∀ z ∈ upperHalfPlane, 2 ≤ ‖z‖ → ‖f z‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ upperHalfPlane, ‖f z‖ ≤ B := by
  let K : Set ℂ := closure upperHalfPlane ∩ closedBall 0 2
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 2).inter_left isClosed_closure
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (hf.mono inter_subset_left)
  refine ⟨max 0 (max A C), le_max_left _ _, ?_⟩
  intro z hz
  by_cases hn : ‖z‖ ≤ 2
  · apply (hA z ?_).trans
      ((le_max_left A C).trans (le_max_right 0 (max A C)))
    exact ⟨subset_closure hz, by simpa using hn⟩
  · exact (hC z hz (le_of_not_ge hn)).trans
      ((le_max_right A C).trans (le_max_right 0 (max A C)))

/-- The derivative of the actual transform has an explicit direction-
independent bound whenever the complex parameter lies outside the ball of
radius two. -/
theorem norm_cauchy_derivative_le_on_exterior {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : ℂ}
    (hz : z ∈ upperHalfPlane) (hn : 2 ≤ ‖z‖) :
    ‖deriv (cauchy φ) z‖ ≤ ‖(Real.pi : ℂ)⁻¹‖ *
      (∫ s in Icc (-1 : ℝ) 1, ‖(height φ s : ℂ)‖) := by
  have hc : ContinuousOn (fun s : ℝ => (height φ s : ℂ)) (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp (height_continuous hφ)).continuousOn
  rw [deriv_cauchy_eq hφ hz, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_cauchy_square_integral_le hc (by linarith)).trans
  apply div_le_self (integral_nonneg fun _ => norm_nonneg _)
  nlinarith [sq_nonneg (‖z‖ - 2)]

/-- The auxiliary derivative has the analogous exterior bound, with its
actual square-height density and normalization. -/
theorem norm_auxiliary_derivative_le_on_exterior {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : ℂ}
    (hz : z ∈ upperHalfPlane) (hn : 2 ≤ ‖z‖) :
    ‖deriv (auxiliary φ) z‖ ≤ ‖(2 * Real.pi : ℂ)⁻¹‖ *
      (∫ s in Icc (-1 : ℝ) 1, ‖(((height φ s) ^ 2 : ℝ) : ℂ)‖) := by
  have hc : ContinuousOn (fun s : ℝ => (((height φ s) ^ 2 : ℝ) : ℂ))
      (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp ((height_continuous hφ).pow 2)).continuousOn
  rw [deriv_auxiliary_eq hφ hz, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_cauchy_square_integral_le hc (by linarith)).trans
  apply div_le_self (integral_nonneg fun _ => norm_nonneg _)
  nlinarith [sq_nonneg (‖z‖ - 2)]

/-- A continuous closed-half-plane extension of the derivative is bounded;
the boundedness is a consequence of the concrete integral, not an input. -/
theorem cauchy_derivative_extension_bounded {φ : ℝ → ℝ} {D : ℂ → ℂ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hD : ContinuousOn D (closure upperHalfPlane))
    (hext : ∀ z ∈ upperHalfPlane, D z = deriv (cauchy φ) z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ upperHalfPlane, ‖D z‖ ≤ B := by
  apply bounded_on_upperHalfPlane_of_continuousOn_closure hD
    (‖(Real.pi : ℂ)⁻¹‖ * (∫ s in Icc (-1 : ℝ) 1, ‖(height φ s : ℂ)‖))
  intro z hz hn
  rw [hext z hz]
  exact norm_cauchy_derivative_le_on_exterior hφ hz hn

/-- Boundedness of a continuous extension of the actual auxiliary derivative. -/
theorem auxiliary_derivative_extension_bounded {φ : ℝ → ℝ} {E : ℂ → ℂ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hE : ContinuousOn E (closure upperHalfPlane))
    (hext : ∀ z ∈ upperHalfPlane, E z = deriv (auxiliary φ) z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ upperHalfPlane, ‖E z‖ ≤ B := by
  apply bounded_on_upperHalfPlane_of_continuousOn_closure hE
    (‖(2 * Real.pi : ℂ)⁻¹‖ *
      (∫ s in Icc (-1 : ℝ) 1, ‖(((height φ s) ^ 2 : ℝ) : ℂ)‖))
  intro z hz hn
  rw [hext z hz]
  exact norm_auxiliary_derivative_le_on_exterior hφ hz hn

private def imaginaryEscape (n : ℕ) : ℂ := (((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I

private theorem imaginaryEscape_mem (n : ℕ) : imaginaryEscape n ∈ upperHalfPlane := by
  change 0 < (imaginaryEscape n).im
  simp [imaginaryEscape]
  positivity

private theorem imaginaryEscape_norm_tendsto :
    Tendsto (fun n => ‖imaginaryEscape n‖) atTop atTop := by
  have hn (n : ℕ) : ‖imaginaryEscape n‖ = (n : ℝ) + 1 := by
    unfold imaginaryEscape
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)]
  simp_rw [hn]
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

/-- Lemma 5.2's quadratic holomorphic identity follows from the linear real
boundary equation and genuine continuous derivative extensions.  Their
boundedness, interior holomorphy and decay are proved from the defining
Cauchy integrals in the proof.  In particular the quadratic identity and a
moment relation are not among this theorem's hypotheses. -/
theorem quadratic_identity_of_boundary_equation {a b : ℝ} {φ : ℝ → ℝ}
    {D E : ℂ → ℂ} (ha : a ≠ 0)
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hDc : ContinuousOn D (closure upperHalfPlane))
    (hEc : ContinuousOn E (closure upperHalfPlane))
    (hD : ∀ z ∈ upperHalfPlane, D z = deriv (cauchy φ) z)
    (hE : ∀ z ∈ upperHalfPlane, E z = deriv (auxiliary φ) z)
    (hDim : ∀ x : ℝ, (D (x : ℂ)).im = -φ x)
    (hEim : ∀ x : ℝ, (E (x : ℂ)).im = -height φ x * φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      (D (x : ℂ)).re = b - a * height φ x) :
    ∀ z ∈ upperHalfPlane,
      deriv (auxiliary φ) z = ((b / a : ℝ) : ℂ) * deriv (cauchy φ) z -
        (deriv (cauchy φ) z) ^ 2 / ((2 * a : ℝ) : ℂ) := by
  let Q : ℂ → ℂ := fun z => E z - ComplexIdentity.holomorphicRHS a b (D z)
  have hDd : DifferentiableOn ℂ D upperHalfPlane :=
    (cauchy_derivative_analyticOnNhd hφ).differentiableOn.congr hD
  have hEd : DifferentiableOn ℂ E upperHalfPlane :=
    (auxiliary_derivative_analyticOnNhd hφ).differentiableOn.congr hE
  have hQc : DiffContOnCl ℂ Q upperHalfPlane := by
    constructor
    · exact hEd.sub (((differentiableOn_const ((b / a : ℝ) : ℂ)).mul hDd).sub
        ((hDd.pow 2).div_const _))
    · exact hEc.sub ((continuousOn_const.mul hDc).sub ((hDc.pow 2).div_const _))
  obtain ⟨BD, hBD, hBD'⟩ := cauchy_derivative_extension_bounded hφ hDc hD
  obtain ⟨BE, _, hBE'⟩ := auxiliary_derivative_extension_bounded hφ hEc hE
  have hQbound : ∀ z ∈ upperHalfPlane,
      ‖Q z‖ ≤ BE + (‖((b / a : ℝ) : ℂ)‖ * BD + BD ^ 2 / ‖((2 * a : ℝ) : ℂ)‖) := by
    intro z hz
    have hpow : ‖D z‖ ^ 2 ≤ BD ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hBD' z hz) 2
    calc
      ‖Q z‖ ≤ ‖E z‖ +
          (‖((b / a : ℝ) : ℂ) * D z‖ + ‖D z ^ 2 / ((2 * a : ℝ) : ℂ)‖) :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ BE + (‖((b / a : ℝ) : ℂ)‖ * BD + BD ^ 2 / ‖((2 * a : ℝ) : ℂ)‖) := by
        rw [norm_mul, norm_div, norm_pow]
        exact add_le_add (hBE' z hz) (add_le_add
          (mul_le_mul_of_nonneg_left (hBD' z hz) (norm_nonneg _))
          (div_le_div_of_nonneg_right hpow (norm_nonneg _)))
  have hQreal : ∀ x : ℝ, (Q (x : ℂ)).im = 0 := by
    intro x
    have hrep : D (x : ℂ) = ((D (x : ℂ)).re : ℂ) + ((-φ x : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hDim x]
    by_cases hx : x ∈ Ioo (-1 : ℝ) 1
    · have hi := ComplexIdentity.boundary_imag_identity a b (height φ x)
        (D (x : ℂ)).re (-φ x) ha (hlinear x hx)
      dsimp [Q]
      rw [hEim x, hrep, hi]
      ring
    · have hx' : 1 ≤ |x| := by
        simp only [mem_Ioo, not_and_or, not_lt] at hx
        rcases hx with hx | hx
        · exact (neg_le_abs x).trans' (by linarith)
        · exact hx.trans (le_abs_self x)
      have hp := hzero x hx'
      dsimp [Q]
      rw [hEim x, hrep]
      simp [ComplexIdentity.holomorphicRHS, hp, pow_two, Complex.div_im,
        Complex.mul_im]
  have hH : ∀ᶠ n : ℕ in atTop, imaginaryEscape n ∈ upperHalfPlane :=
    Eventually.of_forall imaginaryEscape_mem
  have hD0 := cauchy_derivative_tendsto_zero hφ imaginaryEscape_norm_tendsto hH
  have hE0 := auxiliary_derivative_tendsto_zero hφ imaginaryEscape_norm_tendsto hH
  have hQ0 : Tendsto (fun n => Q (imaginaryEscape n)) atTop (𝓝 0) := by
    have h := hE0.sub ((hD0.const_mul ((b / a : ℝ) : ℂ)).sub
      ((hD0.pow 2).div_const ((2 * a : ℝ) : ℂ)))
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_div, sub_zero] at h
    apply h.congr'
    filter_upwards [] with n
    dsimp [Q, ComplexIdentity.holomorphicRHS]
    rw [hD _ (imaginaryEscape_mem n), hE _ (imaginaryEscape_mem n)]
  have hQzero := bounded_holomorphic_real_boundary_eq_zero hQc _ hQbound hQreal hH hQ0
  intro z hz
  have hh := sub_eq_zero.mp (hQzero z hz)
  simpa only [Q, ComplexIdentity.holomorphicRHS, hD z hz, hE z hz] using hh

/-- Concrete moment data constructed from the linear spectral boundary
equation.  The nonlinear moment relation and positivity of `b` are proved
using the preceding quadratic identity and its actual infinity moments. -/
def momentsOfBoundaryEquation {a b : ℝ} {φ : ℝ → ℝ} {D E : ℂ → ℂ}
    (ha : 0 < a) (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hDc : ContinuousOn D (closure upperHalfPlane))
    (hEc : ContinuousOn E (closure upperHalfPlane))
    (hD : ∀ z ∈ upperHalfPlane, D z = deriv (cauchy φ) z)
    (hE : ∀ z ∈ upperHalfPlane, E z = deriv (auxiliary φ) z)
    (hDim : ∀ x : ℝ, (D (x : ℂ)).im = -φ x)
    (hEim : ∀ x : ℝ, (E (x : ℂ)).im = -height φ x * φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      (D (x : ℂ)).re = b - a * height φ x) : Torsion.Moments :=
  momentsOfQuadraticIdentity ha hφ hpos
    (quadratic_identity_of_boundary_equation ha.ne' hφ hzero hDc hEc hD hE
      hDim hEim hlinear)

end Torsion.Spectral

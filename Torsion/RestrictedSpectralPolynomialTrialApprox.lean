module

public import Torsion.RestrictedSpectralPolynomialTrial
public import Torsion.SobolevBoundaryAdmission
public import Torsion.RestrictedSpectralWeakClosure
public import Torsion.RestrictedSpectralInterpolation

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Genuine smooth core approximation of the odd polynomial trial

Flat truncation of `1-x²` supplies compact smooth approximants strictly
inside the interval. Their ordinary derivatives converge in actual L² as
well; the zero extension's endpoint derivative jumps require no regularity
assumption or trace theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

def trialFactor (x : ℝ) : ℝ := x * (1 - x ^ 2 / 2)
def trialFactorDerivative (x : ℝ) : ℝ := 1 - (3 / 2 : ℝ) * x ^ 2
def trialDerivativePolynomial (x : ℝ) : ℝ :=
  1 - (9 / 2 : ℝ) * x ^ 2 + (5 / 2 : ℝ) * x ^ 4

/-- Explicit original-core approximants of the polynomial trial. -/
def oddTrialCore (n : ℕ) (x : ℝ) : ℝ :=
  trialFactor x * BoundaryAdmission.truncation n (1 - x ^ 2)

private theorem trialFactor_hasDerivAt (x : ℝ) :
    HasDerivAt trialFactor (trialFactorDerivative x) x := by
  convert (hasDerivAt_id x).mul
    ((hasDerivAt_const x 1).sub ((hasDerivAt_pow 2 x).div_const 2)) using 1
  all_goals (try funext t)
  all_goals (try dsimp only [trialFactor, trialFactorDerivative, id_eq, Pi.sub_apply, Pi.mul_apply])
  all_goals ring

private theorem trialDistance_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-2 * x) x := by
  convert (hasDerivAt_const x 1).sub (hasDerivAt_pow 2 x) using 1
  all_goals first | rfl | ring

theorem oddTrialCore_contDiff (n : ℕ) : ContDiff ℝ ∞ (oddTrialCore n) := by
  have hr : ContDiff ℝ ∞ trialFactor :=
    contDiff_id.mul (contDiff_const.sub ((contDiff_id.pow 2).div_const 2))
  exact hr.mul ((BoundaryAdmission.truncation_contDiff n).comp (by fun_prop))

theorem oddTrialCore_isCore (n : ℕ) : IsCore (oddTrialCore n) := by
  have hlevel : IsClosed {x : ℝ | BoundaryAdmission.threshold n ≤ 1 - x ^ 2} :=
    isClosed_le continuous_const (by fun_prop)
  have hsupp : Function.support (oddTrialCore n) ⊆
      {x : ℝ | BoundaryAdmission.threshold n ≤ 1 - x ^ 2} := by
    intro x hx
    by_contra h
    exact hx (by
      rw [oddTrialCore, BoundaryAdmission.truncation_zero_of_le n (le_of_not_ge h)]
      ring)
  have htsupp := closure_minimal hsupp hlevel
  have hsub : tsupport (oddTrialCore n) ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx
    have h := htsupp hx
    change BoundaryAdmission.threshold n ≤ 1 - x ^ 2 at h
    have hs : x ^ 2 < 1 := by linarith [BoundaryAdmission.threshold_pos n]
    exact abs_lt.mp ((sq_lt_one_iff_abs_lt_one x).mp hs)
  refine ⟨oddTrialCore_contDiff n, ?_, hsub⟩
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hsub.trans Ioo_subset_Icc_self)

theorem oddTrialCore_deriv (n : ℕ) (x : ℝ) :
    deriv (oddTrialCore n) x =
      trialFactorDerivative x * BoundaryAdmission.truncation n (1 - x ^ 2) +
        trialFactor x * BoundaryAdmission.coefficient n (1 - x ^ 2) * (-2 * x) := by
  have h := (trialFactor_hasDerivAt x).mul
    ((BoundaryAdmission.truncation_hasDerivAt n (1 - x ^ 2)).comp x
      (trialDistance_hasDerivAt x))
  convert h.deriv using 1
  all_goals first | rfl | (dsimp only [oddTrialCore, Function.comp_def, Pi.mul_apply]; ring)

private theorem oddTrialCore_zero_off (n : ℕ) (x : ℝ)
    (hx : x ∉ Icc (-1 : ℝ) 1) : oddTrialCore n x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (Ioo_subset_Icc_self ((oddTrialCore_isCore n).2.2 h)))

private theorem oddTrialCore_deriv_zero_off (n : ℕ) (x : ℝ)
    (hx : x ∉ Icc (-1 : ℝ) 1) : deriv (oddTrialCore n) x = 0 := by
  by_contra h
  exact hx (Ioo_subset_Icc_self ((oddTrialCore_isCore n).2.2 (support_deriv_subset h)))

private theorem truncation_norm_le_one_on_interval (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖BoundaryAdmission.truncation n (1 - x ^ 2)‖ ≤ 1 := by
  have hs : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).mpr (abs_le.mpr hx)
  exact (BoundaryAdmission.truncation_norm_le (by linarith : 0 ≤ 1 - x ^ 2) n).trans
    (by nlinarith [sq_nonneg x])

private theorem integrable_indicator_sq_of_continuous {b : ℝ → ℝ} (hb : Continuous b) :
    Integrable (fun x : ℝ => ((Icc (-1 : ℝ) 1).indicator b x) ^ 2) := by
  have hi : IntegrableOn (fun x => b x ^ 2) (Icc (-1 : ℝ) 1) (volume : Measure ℝ) :=
    (hb.pow 2).integrableOn_Icc
  convert hi.integrable_indicator measurableSet_Icc using 1
  funext x
  by_cases hx : x ∈ Icc (-1 : ℝ) 1 <;> simp [hx]

/-- Actual L² convergence of the smooth restricted core values. -/
theorem oddTrialCore_tendsto_value :
    Tendsto (fun n => eLpNorm (fun x => oddTrialCore n x - oddTrial x) 2 volume)
      atTop (𝓝 0) := by
  let b : ℝ → ℝ := fun x => ‖trialFactor x‖ + ‖oddTrial x‖
  have hr : Continuous trialFactor :=
    continuous_id.mul (continuous_const.sub ((continuous_id.pow 2).div_const 2))
  have hb : Continuous b := hr.norm.add oddTrial_continuous.norm
  apply Torsion.tendsto_eLpNorm_two_of_dominated
    (B := (Icc (-1 : ℝ) 1).indicator b)
  · intro n
    exact (oddTrialCore_contDiff n).continuous.aestronglyMeasurable.sub oddTrial_memLp.aestronglyMeasurable
  · exact integrable_indicator_sq_of_continuous hb
  · intro n
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ Icc (-1 : ℝ) 1
      · rw [indicator_of_mem hx]
        apply (norm_sub_le _ _).trans
        apply add_le_add (b := ‖trialFactor x‖) _ le_rfl
        rw [oddTrialCore, norm_mul]
        exact (mul_le_mul_of_nonneg_left (truncation_norm_le_one_on_interval n hx)
          (norm_nonneg _)).trans_eq (mul_one _)
      · rw [oddTrialCore_zero_off n x hx]
        simp [oddTrial, hx]
  · exact ae_of_all _ fun x => by
      by_cases hx : x ∈ Icc (-1 : ℝ) 1
      · have hs : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).mpr (abs_le.mpr hx)
        have ht := (BoundaryAdmission.truncation_tendsto
          (show 0 ≤ 1 - x ^ 2 by linarith)).const_mul (trialFactor x)
        have hval : trialFactor x * (1 - x ^ 2) = oddTrial x := by
          simp only [oddTrial, indicator_of_mem hx, trialFactor, oddTrialPolynomial]
          ring
        simpa only [oddTrialCore, hval, sub_self] using ht.sub_const (oddTrial x)
      · simp only [oddTrialCore_zero_off _ _ hx, oddTrial, indicator_of_notMem hx,
          sub_self]
        exact tendsto_const_nhds

/-- Actual L² convergence of the smooth core derivatives to the stated
piecewise polynomial derivative. Endpoint values do not affect this limit. -/
theorem oddTrialCore_tendsto_deriv :
    Tendsto (fun n => eLpNorm
      (fun x => deriv (oddTrialCore n) x - oddTrialDerivative x) 2 volume)
      atTop (𝓝 0) := by
  let b : ℝ → ℝ := fun x => ‖trialFactorDerivative x‖ +
    ‖trialFactor x‖ * (2 * ‖x‖) + ‖trialDerivativePolynomial x‖
  have hb : Continuous b := by dsimp [b, trialFactorDerivative, trialFactor, trialDerivativePolynomial]; fun_prop
  apply Torsion.tendsto_eLpNorm_two_of_dominated
    (B := (Icc (-1 : ℝ) 1).indicator b)
  · intro n
    exact ((oddTrialCore_contDiff n).continuous_deriv (by simp)).aestronglyMeasurable.sub
      oddTrialDerivative_memLp.aestronglyMeasurable
  · exact integrable_indicator_sq_of_continuous hb
  · intro n
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ Icc (-1 : ℝ) 1
      · rw [indicator_of_mem hx]
        have hT := truncation_norm_le_one_on_interval n hx
        have hC := BoundaryAdmission.coefficient_norm_le_one n (1 - x ^ 2)
        have hderiv : ‖deriv (oddTrialCore n) x‖ ≤
            ‖trialFactorDerivative x‖ + ‖trialFactor x‖ * (2 * ‖x‖) := by
          rw [oddTrialCore_deriv]
          calc
            _ ≤ ‖trialFactorDerivative x * BoundaryAdmission.truncation n (1 - x ^ 2)‖ +
                ‖trialFactor x * BoundaryAdmission.coefficient n (1 - x ^ 2) * (-2 * x)‖ := norm_add_le _ _
            _ = ‖trialFactorDerivative x‖ * ‖BoundaryAdmission.truncation n (1 - x ^ 2)‖ +
                ‖trialFactor x‖ * ‖BoundaryAdmission.coefficient n (1 - x ^ 2)‖ * (2 * ‖x‖) := by
              simp only [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            _ ≤ _ := by
              have h₁ := mul_le_mul_of_nonneg_left hT (norm_nonneg (trialFactorDerivative x))
              have h₂ := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hC (norm_nonneg (trialFactor x)))
                (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg x))
              nlinarith
        have hD : oddTrialDerivative x = trialDerivativePolynomial x := by
          simp only [oddTrialDerivative, indicator_of_mem hx, trialDerivativePolynomial]
        exact (norm_sub_le _ _).trans (by rw [hD]; exact add_le_add hderiv le_rfl)
      · rw [oddTrialCore_deriv_zero_off n x hx]
        simp [oddTrialDerivative, hx]
  · have hleft : ∀ᵐ x : ℝ ∂volume, x ≠ -1 := by
      simpa using (countable_singleton (-1 : ℝ)).ae_notMem volume
    have hright : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
      simpa using (countable_singleton (1 : ℝ)).ae_notMem volume
    filter_upwards [hleft, hright] with x hxleft hxright
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · have hxo : x ∈ Ioo (-1 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hxleft), lt_of_le_of_ne hx.2 hxright⟩
      have hs : 0 < 1 - x ^ 2 := by
        have hsq := (sq_lt_one_iff_abs_lt_one x).mpr (abs_lt.mpr hxo)
        linarith
      have hT := (BoundaryAdmission.truncation_tendsto hs.le).const_mul (trialFactorDerivative x)
      have hC := ((BoundaryAdmission.coefficient_tendsto_one hs).const_mul (trialFactor x)).mul_const (-2 * x)
      have hlim := hT.add hC
      have hval : trialFactorDerivative x * (1 - x ^ 2) + trialFactor x * 1 * (-2 * x) =
          oddTrialDerivative x := by
        simp only [oddTrialDerivative, indicator_of_mem hx, trialFactorDerivative, trialFactor]
        ring
      simpa only [← oddTrialCore_deriv, hval, sub_self] using! hlim.sub_const (oddTrialDerivative x)
    · simp only [oddTrialCore_deriv_zero_off _ _ hx, oddTrialDerivative,
        indicator_of_notMem hx, sub_self]
      exact tendsto_const_nhds

/-- The explicit zero-extended polynomial is genuinely in the original
restricted form domain and has the interpolated Fourier energy bound. -/
theorem oddTrial_memRestrictedFormDomain_energy_bound :
    MemRestrictedFormDomain oddTrial ∧
      energy oddTrial oddTrial ≤ Real.sqrt ((124 / 1155 : ℝ) * (334 / 315 : ℝ)) := by
  have hvalue := integral_sq_tendsto_of_eLpNorm_sub oddTrial_memLp
    (fun n => (oddTrialCore_isCore n).memLp_value) oddTrialCore_tendsto_value
  have hderivative := integral_sq_tendsto_of_eLpNorm_sub oddTrialDerivative_memLp
    (fun n => ((oddTrialCore_contDiff n).continuous_deriv (by simp)).memLp_of_hasCompactSupport
      (oddTrialCore_isCore n).2.1.deriv) oddTrialCore_tendsto_deriv
  have hlimit := (Real.continuous_sqrt.tendsto _).comp (hvalue.mul hderivative)
  have h := memRestrictedFormDomain_of_core_energy_upper_tendsto oddTrial_memLp
    oddTrialCore_isCore oddTrialCore_tendsto_value
    (Eventually.of_forall fun n => (oddTrialCore_isCore n).energy_le_sqrt_integral_sq_mul_integral_deriv_sq)
    hlimit
  simpa only [oddTrial_integral_sq, oddTrialDerivative_integral_sq] using h

/-- Actual form-domain admission of the explicit odd polynomial trial. -/
theorem oddTrial_memRestrictedFormDomain : MemRestrictedFormDomain oddTrial :=
  oddTrial_memRestrictedFormDomain_energy_bound.1

/-- The explicit actual odd trial lies strictly below the proved even
mean-zero spectral gap, by an exact rational square comparison. -/
theorem oddTrial_energy_lt_even_gap :
    energy oddTrial oddTrial < (63 / 20 : ℝ) * ∫ x : ℝ, oddTrial x ^ 2 := by
  rw [oddTrial_integral_sq]
  apply lt_of_le_of_lt oddTrial_memRestrictedFormDomain_energy_bound.2
  have hs : (Real.sqrt ((124 / 1155 : ℝ) * (334 / 315 : ℝ))) ^ 2 =
      (124 / 1155 : ℝ) * (334 / 315 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg ((124 / 1155 : ℝ) * (334 / 315 : ℝ))
  nlinarith [hs, hn]

end Torsion.Spectral

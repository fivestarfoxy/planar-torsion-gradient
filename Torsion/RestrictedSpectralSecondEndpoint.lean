import Torsion.RestrictedSpectralSecondProfile
import Torsion.RestrictedSpectralEndpointComparison
import Torsion.RestrictedSpectralSemicircleWeak

/-!
# Actual square-root endpoint bounds for the selected second eigenfunction

The proved semicircle weak equation and short-support comparison dominate
the actual selected representative. Its global continuity, including its
zero exterior values, is a consequence rather than an additional input.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion.Spectral

private theorem secondEigenfunction_nonpos_left (x : ℝ) (hx : x ≤ 0) :
    secondEigenfunction x ≤ 0 := by
  by_cases hext : 1 ≤ |x|
  · rw [secondEigenfunction_zero_exterior x hext]
  · have hxi := abs_lt.mp (lt_of_not_ge hext)
    by_cases hx0 : x = 0
    · rw [hx0]
      have h := secondEigenfunction_odd (0 : ℝ)
      simp only [neg_zero] at h
      linarith
    · have hxn : x < 0 := lt_of_le_of_ne hx hx0
      have h := secondEigenfunction_nonneg (-x) ⟨neg_pos.mpr hxn, by linarith [hxi.1]⟩
      rw [secondEigenfunction_odd x] at h
      linarith

/-- The actual second eigenfunction is dominated everywhere by a constant
multiple of the concrete semicircle, with no assumed endpoint regularity. -/
theorem secondEigenfunction_semicircle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      |secondEigenfunction x| ≤ C * semicircleBarrier x :=
  secondEigenfunction_isRestrictedEigenfunction.exists_semicircle_bound_of_weak_barrier
    semicircleBarrier_memRestrictedFormDomain semicircleBarrier_weak_equation
    secondEigenfunction_contDiffOn.continuousOn secondEigenfunction_odd
    secondEigenfunction_nonpos_left secondEigenfunction_zero_exterior

/-- The endpoint estimate uses the ordinary original square-root profile. -/
theorem secondEigenfunction_sqrt_boundary_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      |secondEigenfunction x| ≤ C * Real.sqrt (1 - x ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := secondEigenfunction_semicircle_bound
  exact ⟨C, hC, fun x => by simpa only [semicircleBarrier_eq_sqrt] using hbound x⟩

/-- The actual selected second eigenfunction is continuous on all of ℝ,
including the two support endpoints and the zero exterior. -/
theorem secondEigenfunction_continuous : Continuous secondEigenfunction := by
  obtain ⟨C, _, hbound⟩ := secondEigenfunction_semicircle_bound
  exact continuous_of_semicircle_bound secondEigenfunction_contDiffOn.continuousOn
    secondEigenfunction_zero_exterior hbound

/-- The same actual square-root bound also proves global boundedness. -/
theorem secondEigenfunction_bounded : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |secondEigenfunction x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := secondEigenfunction_semicircle_bound
  refine ⟨C, hC, fun x => (hbound x).trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (semicircleBarrier_le_one x) hC.le).trans_eq (mul_one C)

theorem secondEigenfunction_tendsto_one : Tendsto secondEigenfunction (𝓝 1) (𝓝 0) := by
  simpa only [secondEigenfunction_zero_exterior 1 (by norm_num)] using
    secondEigenfunction_continuous.tendsto (1 : ℝ)

theorem secondEigenfunction_tendsto_neg_one : Tendsto secondEigenfunction (𝓝 (-1)) (𝓝 0) := by
  simpa only [secondEigenfunction_zero_exterior (-1) (by norm_num)] using
    secondEigenfunction_continuous.tendsto (-1 : ℝ)

end Torsion.Spectral

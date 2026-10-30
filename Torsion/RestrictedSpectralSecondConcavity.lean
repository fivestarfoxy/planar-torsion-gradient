import Torsion.RestrictedSpectralSecondExteriorIntegrability
import Torsion.RestrictedSpectralConcavity

/-!
# Actual strict concavity of the constructed second eigenfunction

All hypotheses of the operator composition and sign theorems are discharged
by the constructed weak eigenpair, its proved regular representative, and
its actual square-root endpoint estimate. No concavity or Hölder input is
assumed.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff SchwartzMap

namespace Torsion.Spectral

theorem secondEigenfunction_nonneg_half_ae :
    0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] secondEigenfunction := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  by_cases h : x < 1
  · exact secondEigenfunction_nonneg x ⟨hx, h⟩
  · rw [secondEigenfunction_zero_exterior x ((le_of_not_gt h).trans (le_abs_self x))]
    exact le_rfl

theorem secondEigenfunction_global_schwartz_equation (S : 𝓢(ℝ, ℝ)) :
    energy secondEigenfunction S = ∫ x : ℝ,
      (secondEigenvalue * secondEigenfunction x - exteriorResidualZero secondEigenfunction x) * S x :=
  secondEigenfunction_isRestrictedEigenfunction.global_schwartz_equation
    secondEigenfunction_exteriorResidualZero_integrable S

/-- The actual pointwise composition identity throughout the spectral interval. -/
theorem secondEigenfunction_second_deriv_eq (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    deriv (deriv secondEigenfunction) x = -secondEigenvalue ^ 2 * secondEigenfunction x -
      (1 / Real.pi) * ∫ y : ℝ, exteriorResidualZero secondEigenfunction y / (x - y) ^ 2 :=
  secondEigenfunction_isRestrictedEigenfunction.second_deriv_eq_exterior_residual
    secondEigenfunction_contDiffOn secondEigenfunction_exteriorResidualZero_integrable x hx

theorem secondEigenfunction_second_deriv_neg (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv secondEigenfunction) x < 0 :=
  secondEigenfunction_isRestrictedEigenfunction.second_deriv_neg secondEigenfunction_odd
    secondEigenfunction_nonneg_half_ae secondEigenfunction_contDiffOn
    secondEigenfunction_exteriorResidualZero_integrable x hx

theorem secondEigenfunction_strictConcaveOn_Ioo :
    StrictConcaveOn ℝ (Ioo (0 : ℝ) 1) secondEigenfunction :=
  secondEigenfunction_isRestrictedEigenfunction.strictConcaveOn_Ioo secondEigenfunction_odd
    secondEigenfunction_nonneg_half_ae secondEigenfunction_contDiffOn
    secondEigenfunction_exteriorResidualZero_integrable

/-- Strict concavity includes the actual zero endpoint values. -/
theorem secondEigenfunction_strictConcaveOn :
    StrictConcaveOn ℝ (Icc (0 : ℝ) 1) secondEigenfunction :=
  secondEigenfunction_isRestrictedEigenfunction.strictConcaveOn_Icc secondEigenfunction_odd
    secondEigenfunction_nonneg_half_ae secondEigenfunction_contDiffOn
    secondEigenfunction_continuous.continuousOn secondEigenfunction_exteriorResidualZero_integrable

theorem secondEigenfunction_concaveOn_Ioo :
    ConcaveOn ℝ (Ioo (0 : ℝ) 1) secondEigenfunction :=
  secondEigenfunction_strictConcaveOn_Ioo.concaveOn

theorem secondEigenfunction_concaveOn :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) secondEigenfunction :=
  secondEigenfunction_strictConcaveOn.concaveOn

end Torsion.Spectral

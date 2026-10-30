module

public import Torsion.RestrictedSpectralSecondConcavity
public import Torsion.RestrictedSpectralConcaveHolder
public import Torsion.RestrictedSpectralHilbert

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Global one-half Hölder regularity of the actual second eigenfunction

The independently proved square-root barrier estimate and the proved actual
concavity supply the global modulus, including both support endpoints and
the zero exterior. The resulting spectral profile also supplies the actual
linear Hilbert equation used by the existing Cauchy construction.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion.Spectral

/-- The constructed second eigenfunction, with its original zero exterior,
is globally one-half Hölder. This conclusion has no unproved spectral input. -/
theorem secondEigenfunction_holder_half :
    ∃ C : ℝ≥0, HolderWith C (1 / 2) secondEigenfunction := by
  obtain ⟨K, hK, hbound⟩ := secondEigenfunction_semicircle_bound
  apply exists_holder_half_of_analytic_concave_odd_local_endpoint_bound
    (K := 2 * K) (δ := 1) secondEigenfunction_analyticOnNhd
    secondEigenfunction_concaveOn_Ioo secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_nonneg (by norm_num)
  intro t ht _
  have hsq : semicircleBarrier t ^ 2 ≤ 2 * (1 - t) := by
    rw [semicircleBarrier_sq]
    apply max_le
    · nlinarith [sq_nonneg (t - 1)]
    · linarith [ht.2]
  have hroot : semicircleBarrier t ≤ 2 * Real.sqrt (1 - t) := by
    have hr := Real.sq_sqrt (sub_nonneg.2 ht.2)
    nlinarith [semicircleBarrier_nonneg t, Real.sqrt_nonneg (1 - t)]
  calc
    secondEigenfunction t ≤ |secondEigenfunction t| := le_abs_self _
    _ ≤ K * semicircleBarrier t := hbound t
    _ ≤ K * (2 * Real.sqrt (1 - t)) := mul_le_mul_of_nonneg_left hroot hK.le
    _ = (2 * K) * Real.sqrt (1 - t) := by ring

/-- The previously conditional pointwise Hilbert input is now constructed
for the selected actual second profile. -/
theorem secondEigenfunction_linear_hilbert_equation :
    ∃! b : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe secondEigenfunction x =
        secondEigenvalue * height secondEigenfunction x - b := by
  obtain ⟨C, hC⟩ := secondEigenfunction_holder_half
  exact secondEigenfunction_isRestrictedEigenfunction.linear_hilbert_equation hC
    (by norm_num) secondEigenfunction_odd

/-- A normalized, simple, odd, positive, analytic, concave, globally Hölder
second profile exists for the original concrete restricted Fourier problem.
Every displayed spectral property is proved, rather than an explicit input. -/
theorem exists_second_restricted_spectral_profile :
    ∃ (φ : ℝ → ℝ) (C : ℝ≥0),
      IsRestrictedEigenfunction secondEigenvalue φ ∧ Function.Odd φ ∧
      (∀ x : ℝ, 1 ≤ |x| → φ x = 0) ∧ (∫ x : ℝ, φ x ^ 2) = 1 ∧
      AnalyticOnNhd ℝ φ (Ioo (-1 : ℝ) 1) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) ∧
      StrictConcaveOn ℝ (Icc (0 : ℝ) 1) φ ∧ HolderWith C (1 / 2) φ ∧
      (∀ g : ℝ → ℝ, IsRestrictedEigenfunction secondEigenvalue g →
        ∃ c : ℝ, g =ᵐ[volume] fun x => c * φ x) := by
  obtain ⟨C, hC⟩ := secondEigenfunction_holder_half
  exact ⟨secondEigenfunction, C, secondEigenfunction_isRestrictedEigenfunction,
    secondEigenfunction_odd, secondEigenfunction_zero_exterior,
    secondEigenfunction_normalized, secondEigenfunction_analyticOnNhd,
    secondEigenfunction_pos, secondEigenfunction_strictConcaveOn, hC,
    fun _ hg => secondEigenfunction_simple hg⟩

end Torsion.Spectral

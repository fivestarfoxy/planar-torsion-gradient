module

public import Torsion.RestrictedSpectralSecondIdentification
public import Torsion.RestrictedSpectralPolynomialTrialApprox

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The actual second restricted eigenpair is the simple least odd pair

An admitted polynomial trial lies strictly below the proved even mean-zero
gap. This discharges the quantitative input of the parity comparison, so the
least odd and second variational eigenvalues are genuinely identified.
All choices below come from proved existence for the original Fourier form.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

theorem leastOddEigenvalue_lt_even_gap : leastOddEigenvalue < (63 / 20 : ℝ) := by
  have hlower := leastOddEigenvalue_variational oddTrial
    oddTrial_memRestrictedFormDomain oddTrial_odd
  have hlt := lt_of_le_of_lt hlower oddTrial_energy_lt_even_gap
  have hm : 0 < ∫ x : ℝ, oddTrial x ^ 2 := by rw [oddTrial_integral_sq]; norm_num
  exact (mul_lt_mul_iff_of_pos_right hm).mp hlt

theorem secondEigenvalue_lt_even_gap : secondEigenvalue < (63 / 20 : ℝ) :=
  lt_of_le_of_lt secondEigenvalue_le_leastOddEigenvalue leastOddEigenvalue_lt_even_gap

theorem firstEigenvalue_le_of_isRestrictedEigenfunction {a : ℝ} {φ : ℝ → ℝ}
    (hφ : IsRestrictedEigenfunction a φ) : firstEigenvalue ≤ a := by
  have h := firstEigenvalue_variational φ hφ.1
  have heq : energy φ φ = a * ∫ x : ℝ, φ x ^ 2 := by
    simpa only [← pow_two] using hφ.2.2 φ hφ.1
  rw [heq] at h
  have hm : 0 < ∫ x : ℝ, φ x ^ 2 := by
    simpa only [← pow_two] using hφ.square_integral_pos
  exact (mul_le_mul_iff_of_pos_right hm).mp h

/-- No genuine eigenvalue other than the constructed first value lies below
the constructed second value. This identifies the variational indexing
directly in terms of the original weak eigenfunction predicate. -/
theorem secondEigenvalue_le_of_isRestrictedEigenfunction_ne_first {a : ℝ} {φ : ℝ → ℝ}
    (hφ : IsRestrictedEigenfunction a φ) (hne : a ≠ firstEigenvalue) :
    secondEigenvalue ≤ a := by
  have h := secondEigenvalue_minimum φ hφ.1
    (firstEigenfunctionL2_isRestrictedEigenfunction.orthogonal hφ hne.symm)
  have heq : energy φ φ = a * ∫ x : ℝ, φ x ^ 2 := by
    simpa only [← pow_two] using hφ.2.2 φ hφ.1
  rw [heq] at h
  have hm : 0 < ∫ x : ℝ, φ x ^ 2 := by
    simpa only [← pow_two] using hφ.square_integral_pos
  exact (mul_le_mul_iff_of_pos_right hm).mp h

/-- The actually constructed second variational value is exactly the
actually constructed least odd value. -/
theorem leastOddEigenvalue_eq_secondEigenvalue : leastOddEigenvalue = secondEigenvalue :=
  leastOddEigenvalue_eq_secondEigenvalue_of_lt_even_gap secondEigenvalue_lt_even_gap

theorem secondEigenfunctionL2_eq_oddPart_ae :
    secondEigenfunctionL2 =ᵐ[volume] restrictedOddPart secondEigenfunctionL2 :=
  secondEigenfunctionL2_eq_oddPart_ae_of_lt_even_gap secondEigenvalue_lt_even_gap

/-- An explicitly odd normalized representative of the actual second
eigenpair, with the original zero exterior convention and chosen positive
half-line sign. Pointwise regularization is supplied separately. -/
def secondOddEigenfunctionL2 : ℝ → ℝ := leastOddEigenfunctionL2

theorem secondOddEigenfunctionL2_isRestrictedEigenfunction :
    IsRestrictedEigenfunction secondEigenvalue secondOddEigenfunctionL2 := by
  rw [← leastOddEigenvalue_eq_secondEigenvalue]
  exact leastOddEigenfunctionL2_isRestrictedEigenfunction

theorem secondOddEigenfunctionL2_odd : Function.Odd secondOddEigenfunctionL2 :=
  leastOddEigenfunctionL2_odd

theorem secondOddEigenfunctionL2_zero_exterior (x : ℝ) (hx : 1 ≤ |x|) :
    secondOddEigenfunctionL2 x = 0 := leastOddEigenfunctionL2_zero_exterior x hx

theorem secondOddEigenfunctionL2_nonneg_half (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ secondOddEigenfunctionL2 x := leastOddEigenfunctionL2_nonneg_half x hx

theorem secondOddEigenfunctionL2_normalized :
    (∫ x : ℝ, secondOddEigenfunctionL2 x ^ 2) = 1 := leastOddEigenfunctionL2_normalized

theorem secondOddEigenfunctionL2_half_mass_pos :
    0 < ∫ x in Ioi (0 : ℝ), secondOddEigenfunctionL2 x := leastOddEigenfunctionL2_half_mass_pos

theorem secondOddEigenfunctionL2_pos_ae :
    ∀ᵐ x : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < secondOddEigenfunctionL2 x :=
  leastOddEigenfunctionL2_pos_ae

/-- Simplicity of the full actual second eigenspace, modulo a.e. equality.
This is no longer conditional on a trial bound or an assumed parity theorem. -/
theorem secondOddEigenfunctionL2_simple {g : ℝ → ℝ}
    (hg : IsRestrictedEigenfunction secondEigenvalue g) :
    ∃ c : ℝ, g =ᵐ[volume] fun x => c * secondOddEigenfunctionL2 x :=
  secondEigenfunction_simple_of_lt_even_gap secondEigenvalue_lt_even_gap hg

/-- A genuine second eigenfunction with the proved symmetry, normalization,
sign and simplicity properties, over the original concrete definitions. -/
theorem exists_second_odd_nonnegative_simple_restricted_eigenfunction :
    ∃ φ : ℝ → ℝ, IsRestrictedEigenfunction secondEigenvalue φ ∧
      Function.Odd φ ∧ (∀ x : ℝ, 1 ≤ |x| → φ x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ φ x) ∧ (∫ x : ℝ, φ x ^ 2) = 1 ∧
      (∀ᵐ x : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < φ x) ∧
      (∀ g : ℝ → ℝ, IsRestrictedEigenfunction secondEigenvalue g →
        ∃ c : ℝ, g =ᵐ[volume] fun x => c * φ x) :=
  ⟨secondOddEigenfunctionL2, secondOddEigenfunctionL2_isRestrictedEigenfunction,
    secondOddEigenfunctionL2_odd, secondOddEigenfunctionL2_zero_exterior,
    secondOddEigenfunctionL2_nonneg_half, secondOddEigenfunctionL2_normalized,
    secondOddEigenfunctionL2_pos_ae, fun _ hg => secondOddEigenfunctionL2_simple hg⟩

end Torsion.Spectral

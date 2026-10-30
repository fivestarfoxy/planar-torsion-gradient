import Torsion.RestrictedSpectralGroundState
import Torsion.RestrictedSpectralGroundSign

/-!
# Selected first and second variational restricted eigenpairs

The choices below come from proved existence and min--max theorems for the
original restricted Fourier problem. The first profile is chosen even and
nonnegative. The second is its normalized orthogonal variational successor.
No simplicity, second-eigenfunction parity or pointwise regularity is
postulated by these definitions.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Torsion.Spectral

/-- Existence of an actual normalized second variational eigenpair,
with an even nonnegative normalized ground-state certificate. The indexing
counts multiplicity. -/
theorem exists_second_variational_eigenpair :
    ∃ a : ℝ, ∃ φ : ℝ → ℝ, IsRestrictedEigenfunction a φ ∧
      (∫ x : ℝ, φ x ^ 2) = 1 ∧
      ∃ a₁ : ℝ, ∃ φ₁ : ℝ → ℝ, IsRestrictedEigenfunction a₁ φ₁ ∧
        0 < a₁ ∧ a₁ ≤ a ∧ (∫ x : ℝ, φ₁ x ^ 2) = 1 ∧
        (∫ x : ℝ, φ₁ x * φ x) = 0 ∧ Function.Even φ₁ ∧
        (∀ x : ℝ, 0 ≤ φ₁ x) ∧
        (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
          a₁ * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) ∧
        (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
          (∫ x : ℝ, φ₁ x * ψ x) = 0 →
            a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) := by
  obtain ⟨a₁, a₂, ha₁, horder, φ₁, φ₂, hE₁, hE₂, hnorm₁, hnorm₂,
      horth, heven, hnonneg, hmin₁, hmin₂⟩ :=
    exists_first_two_restricted_eigenpairs_even_nonnegative_first
  exact ⟨a₂, φ₂, hE₂, hnorm₂, a₁, φ₁, hE₁, ha₁, horder,
    hnorm₁, horth, heven, hnonneg, hmin₁, hmin₂⟩

/-- An actual selected second variational eigenvalue of the restricted
Fourier problem. Its existence and variational order are proved. -/
def secondEigenvalue : ℝ := Classical.choose exists_second_variational_eigenpair

/-- A selected normalized L² representative of the actual second eigenpair.
Pointwise regularity is not asserted for an arbitrary a.e. representative;
selection of the regular spectral profile remains a separate theorem. -/
def secondEigenfunctionL2 : ℝ → ℝ :=
  Classical.choose (Classical.choose_spec exists_second_variational_eigenpair)

theorem secondEigenfunctionL2_isRestrictedEigenfunction :
    IsRestrictedEigenfunction secondEigenvalue secondEigenfunctionL2 :=
  (Classical.choose_spec (Classical.choose_spec exists_second_variational_eigenpair)).1

theorem secondEigenfunctionL2_normalized :
    (∫ x : ℝ, secondEigenfunctionL2 x ^ 2) = 1 :=
  (Classical.choose_spec (Classical.choose_spec exists_second_variational_eigenpair)).2.1

/-- Original Fourier min--max characterization of the selected second
pair relative to an actual even nonnegative normalized ground state. -/
theorem secondEigenvalue_variational :
    ∃ a₁ : ℝ, ∃ φ₁ : ℝ → ℝ, IsRestrictedEigenfunction a₁ φ₁ ∧
      0 < a₁ ∧ a₁ ≤ secondEigenvalue ∧ (∫ x : ℝ, φ₁ x ^ 2) = 1 ∧
      (∫ x : ℝ, φ₁ x * secondEigenfunctionL2 x) = 0 ∧ Function.Even φ₁ ∧
      (∀ x : ℝ, 0 ≤ φ₁ x) ∧
      (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
        a₁ * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) ∧
      (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
        (∫ x : ℝ, φ₁ x * ψ x) = 0 →
          secondEigenvalue * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) :=
  (Classical.choose_spec (Classical.choose_spec exists_second_variational_eigenpair)).2.2

theorem secondEigenvalue_pos : 0 < secondEigenvalue :=
  secondEigenfunctionL2_isRestrictedEigenfunction.eigenvalue_pos

theorem secondEigenvalue_ge_pi_div_eight : Real.pi / 8 ≤ secondEigenvalue :=
  secondEigenfunctionL2_isRestrictedEigenfunction.eigenvalue_ge_pi_div_eight

/-- Every actual odd weak eigenfunction has eigenvalue at least the
constructed second variational value. The reverse inequality for the
least odd eigenpair, and hence second-eigenfunction oddness, is not asserted. -/
theorem secondEigenvalue_le_of_odd_eigenfunction {a : ℝ} {φ : ℝ → ℝ}
    (hφ : IsRestrictedEigenfunction a φ) (hodd : Function.Odd φ) :
    secondEigenvalue ≤ a := by
  obtain ⟨a₁, φ₁, _, _, _, _, _, heven, _, _, hmin⟩ := secondEigenvalue_variational
  have h := hmin φ hφ.1 (integral_mul_eq_zero_of_even_odd heven hodd)
  have hsq : 0 < ∫ x : ℝ, φ x ^ 2 := by
    simpa only [pow_two] using hφ.square_integral_pos
  have heq : energy φ φ = a * ∫ x : ℝ, φ x ^ 2 := by
    simpa only [pow_two] using hφ.2.2 φ hφ.1
  rw [heq] at h
  exact (mul_le_mul_right hsq).mp h


/-- The actual first variational value chosen along with the second pair. -/
def firstEigenvalue : ℝ := Classical.choose secondEigenvalue_variational

def firstEigenfunctionL2 : ℝ → ℝ :=
  Classical.choose (Classical.choose_spec secondEigenvalue_variational)

private theorem selectedGround_spec :
    IsRestrictedEigenfunction firstEigenvalue firstEigenfunctionL2 ∧
      0 < firstEigenvalue ∧ firstEigenvalue ≤ secondEigenvalue ∧
      (∫ x : ℝ, firstEigenfunctionL2 x ^ 2) = 1 ∧
      (∫ x : ℝ, firstEigenfunctionL2 x * secondEigenfunctionL2 x) = 0 ∧
      Function.Even firstEigenfunctionL2 ∧ (∀ x : ℝ, 0 ≤ firstEigenfunctionL2 x) ∧
      (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
        firstEigenvalue * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) ∧
      (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
        (∫ x : ℝ, firstEigenfunctionL2 x * ψ x) = 0 →
          secondEigenvalue * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) :=
  Classical.choose_spec (Classical.choose_spec secondEigenvalue_variational)

theorem firstEigenfunctionL2_isRestrictedEigenfunction :
    IsRestrictedEigenfunction firstEigenvalue firstEigenfunctionL2 := selectedGround_spec.1

theorem firstEigenfunctionL2_even : Function.Even firstEigenfunctionL2 :=
  selectedGround_spec.2.2.2.2.2.1

theorem firstEigenfunctionL2_nonneg (x : ℝ) : 0 ≤ firstEigenfunctionL2 x :=
  selectedGround_spec.2.2.2.2.2.2.1 x

theorem firstEigenfunctionL2_normalized : (∫ x : ℝ, firstEigenfunctionL2 x ^ 2) = 1 :=
  selectedGround_spec.2.2.2.1

theorem firstEigenvalue_variational (ψ : ℝ → ℝ) (hψ : MemRestrictedFormDomain ψ) :
    firstEigenvalue * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ :=
  selectedGround_spec.2.2.2.2.2.2.2.1 ψ hψ

theorem first_secondEigenfunctionL2_orthogonal :
    (∫ x : ℝ, firstEigenfunctionL2 x * secondEigenfunctionL2 x) = 0 :=
  selectedGround_spec.2.2.2.2.1

theorem secondEigenvalue_minimum (ψ : ℝ → ℝ) (hψ : MemRestrictedFormDomain ψ)
    (horth : (∫ x : ℝ, firstEigenfunctionL2 x * ψ x) = 0) :
    secondEigenvalue * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ :=
  selectedGround_spec.2.2.2.2.2.2.2.2 ψ hψ horth

/-- The constructed second value is strictly above the first: this uses
the proved simplicity of the actual ground eigenspace, not an assumption
that the constructed eigenvalues are distinct. -/
theorem firstEigenvalue_lt_secondEigenvalue : firstEigenvalue < secondEigenvalue := by
  have hne := firstEigenfunctionL2_isRestrictedEigenfunction.eigenvalue_ne_of_orthogonal_to_ground
    secondEigenfunctionL2_isRestrictedEigenfunction firstEigenvalue_variational
    selectedGround_spec.2.2.2.2.1
  exact lt_of_le_of_ne selectedGround_spec.2.2.1 (Ne.symm hne)

/-- Simplicity of the actually selected first eigenspace, modulo the
original L² representative relation. -/
theorem firstEigenfunctionL2_simple {g : ℝ → ℝ}
    (hg : IsRestrictedEigenfunction firstEigenvalue g) :
    ∃ c : ℝ, g =ᵐ[volume] fun x => c * firstEigenfunctionL2 x := by
  exact ⟨(∫ x : ℝ, g x) / (∫ x : ℝ, firstEigenfunctionL2 x),
    firstEigenfunctionL2_isRestrictedEigenfunction.ae_eq_integral_ratio_mul_of_rayleigh_lower_bound
      hg firstEigenvalue_variational⟩

end Torsion.Spectral

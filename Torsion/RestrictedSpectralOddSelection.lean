module

public import Torsion.RestrictedSpectralOddGroundState
public import Torsion.RestrictedSpectralOddGroundSign
public import Torsion.RestrictedSpectralOddPositivity
public import Torsion.RestrictedSpectralSelection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Selection of the constructed least odd eigenpair

These choices use the proved compact-resolvent construction and the proved
folded-absolute contraction of the original Fourier form. They do not impose
regularity on an arbitrary L² representative. Identification with the second
variational eigenvalue is a separate theorem.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- The actual least odd restricted eigenvalue. -/
def leastOddEigenvalue : ℝ :=
  Classical.choose exists_least_odd_nonnegative_half_restricted_eigenpair

/-- A normalized odd representative, nonnegative on the positive half line
and zero outside the interval, selected from actual proved existence. -/
def leastOddEigenfunctionL2 : ℝ → ℝ :=
  Classical.choose
    (Classical.choose_spec exists_least_odd_nonnegative_half_restricted_eigenpair).2

private theorem selectedLeastOdd_spec :
    IsRestrictedEigenfunction leastOddEigenvalue leastOddEigenfunctionL2 ∧
      Function.Odd leastOddEigenfunctionL2 ∧
      (∀ x : ℝ, 1 ≤ |x| → leastOddEigenfunctionL2 x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ leastOddEigenfunctionL2 x) ∧
      (∫ x : ℝ, leastOddEigenfunctionL2 x ^ 2) = 1 ∧
      (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → Function.Odd ψ →
        leastOddEigenvalue * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) :=
  Classical.choose_spec
    (Classical.choose_spec exists_least_odd_nonnegative_half_restricted_eigenpair).2

theorem leastOddEigenvalue_pos : 0 < leastOddEigenvalue :=
  (Classical.choose_spec exists_least_odd_nonnegative_half_restricted_eigenpair).1

theorem leastOddEigenfunctionL2_isRestrictedEigenfunction :
    IsRestrictedEigenfunction leastOddEigenvalue leastOddEigenfunctionL2 :=
  selectedLeastOdd_spec.1

theorem leastOddEigenfunctionL2_odd : Function.Odd leastOddEigenfunctionL2 :=
  selectedLeastOdd_spec.2.1

theorem leastOddEigenfunctionL2_zero_exterior (x : ℝ) (hx : 1 ≤ |x|) :
    leastOddEigenfunctionL2 x = 0 := selectedLeastOdd_spec.2.2.1 x hx

theorem leastOddEigenfunctionL2_nonneg_half (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ leastOddEigenfunctionL2 x := selectedLeastOdd_spec.2.2.2.1 x hx

theorem leastOddEigenfunctionL2_normalized :
    (∫ x : ℝ, leastOddEigenfunctionL2 x ^ 2) = 1 :=
  selectedLeastOdd_spec.2.2.2.2.1

theorem leastOddEigenvalue_variational (ψ : ℝ → ℝ)
    (hψ : MemRestrictedFormDomain ψ) (hodd : Function.Odd ψ) :
    leastOddEigenvalue * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ :=
  selectedLeastOdd_spec.2.2.2.2.2 ψ hψ hodd

/-- The ordinary second variational value is no larger than the constructed
least odd value. No reverse comparison is implicit in this statement. -/
theorem secondEigenvalue_le_leastOddEigenvalue :
    secondEigenvalue ≤ leastOddEigenvalue :=
  secondEigenvalue_le_of_odd_eigenfunction
    leastOddEigenfunctionL2_isRestrictedEigenfunction leastOddEigenfunctionL2_odd

/-- The selected profile has positive actual mass on the positive half line.
This uses its proved sign and nonvanishing, without asserting pointwise
strict positivity. -/
theorem leastOddEigenfunctionL2_half_mass_pos :
    0 < ∫ x in Ioi (0 : ℝ), leastOddEigenfunctionL2 x := by
  have hnonneg : 0 ≤ ∫ x in Ioi (0 : ℝ), leastOddEigenfunctionL2 x := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact leastOddEigenfunctionL2_nonneg_half x hx.le
  have hne :=
    leastOddEigenfunctionL2_isRestrictedEigenfunction.integral_half_ne_zero_of_odd_rayleigh_lower_bound
      leastOddEigenfunctionL2_odd leastOddEigenvalue_variational
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Simplicity inside the actual odd eigenspace at the selected least odd
value. Full second-eigenspace simplicity also needs the parity comparison. -/
theorem leastOddEigenfunctionL2_simple {g : ℝ → ℝ}
    (hg : IsRestrictedEigenfunction leastOddEigenvalue g) (hodd : Function.Odd g) :
    ∃ c : ℝ, g =ᵐ[volume] fun x => c * leastOddEigenfunctionL2 x := by
  exact ⟨(∫ x in Ioi (0 : ℝ), g x) /
      (∫ x in Ioi (0 : ℝ), leastOddEigenfunctionL2 x),
    leastOddEigenfunctionL2_isRestrictedEigenfunction.ae_eq_half_integral_ratio_mul_of_odd_rayleigh_lower_bound
      hg leastOddEigenfunctionL2_odd hodd leastOddEigenvalue_variational⟩

/-- Strict positivity almost everywhere on the open positive half of the
original interval, established by the genuine odd-kernel perturbation. -/
theorem leastOddEigenfunctionL2_pos_ae :
    ∀ᵐ x : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < leastOddEigenfunctionL2 x := by
  apply leastOddEigenfunctionL2_isRestrictedEigenfunction.pos_ae_of_odd_rayleigh_lower_bound
    leastOddEigenfunctionL2_odd leastOddEigenvalue_variational
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact leastOddEigenfunctionL2_nonneg_half x hx.le

end Torsion.Spectral

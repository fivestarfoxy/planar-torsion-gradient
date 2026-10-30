module

public import Torsion.RestrictedSpectralOddMinimizer
public import Torsion.RestrictedSpectralOddLattice
public import Torsion.RestrictedSpectralOddEigenpair

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A least odd eigenfunction nonnegative on the positive half line

The actual folded-absolute contraction and the actual odd-sector minimum
force equality of the original Fourier energy. The proved odd-sector Euler
argument then gives the full original weak equation at the same eigenvalue.
No positivity-improving or second-eigenvalue identification is asserted.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform

namespace Torsion.Spectral

/-- Folding an actual least odd eigenfunction preserves its original weak
eigenfunction equation and its eigenvalue. -/
theorem IsRestrictedEigenfunction.oddFoldAbs_of_odd_rayleigh_lower_bound
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hodd : Function.Odd f)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → Function.Odd ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) :
    IsRestrictedEigenfunction a (oddFoldAbs f) := by
  have hfold := hf.1.oddFoldAbs_energy_le hodd
  apply isRestrictedEigenfunction_of_odd_rayleigh_minimum hfold.1 (oddFoldAbs_odd hodd)
    (oddFoldAbs_not_ae_zero hf.2.1) hlower
  apply le_antisymm
  · calc
      energy (oddFoldAbs f) (oddFoldAbs f) ≤ energy f f := hfold.2
      _ = a * ∫ x : ℝ, f x ^ 2 := by simpa only [pow_two] using hf.2.2 f hf.1
      _ = a * ∫ x : ℝ, oddFoldAbs f x ^ 2 := by simp only [oddFoldAbs_sq]
  · exact hlower _ hfold.1 (oddFoldAbs_odd hodd)

/-- There is an actual normalized least odd weak restricted eigenfunction
which is pointwise nonnegative on the positive half line and globally zero
outside the original interval. The odd-sector minimum is unchanged. -/
theorem exists_least_odd_nonnegative_half_restricted_eigenpair :
    ∃ a : ℝ, 0 < a ∧ ∃ φ : ℝ → ℝ,
      IsRestrictedEigenfunction a φ ∧ Function.Odd φ ∧
      (∀ x : ℝ, 1 ≤ |x| → φ x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ φ x) ∧
      (∫ x : ℝ, φ x ^ 2) = 1 ∧
      (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → Function.Odd ψ →
        a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) := by
  obtain ⟨a, ha, f, hf, hodd, hzero, hmass, hlower⟩ := exists_least_odd_restricted_eigenpair
  refine ⟨a, ha, oddFoldAbs f, hf.oddFoldAbs_of_odd_rayleigh_lower_bound hodd hlower,
    oddFoldAbs_odd hodd, ?_, (fun x hx => oddFoldAbs_nonneg f hx), ?_, hlower⟩
  · intro x hx
    have h := oddFoldAbs_norm f x
    rw [hzero x hx, norm_zero] at h
    exact norm_eq_zero.mp h
  · simpa only [oddFoldAbs_sq] using hmass

end Torsion.Spectral

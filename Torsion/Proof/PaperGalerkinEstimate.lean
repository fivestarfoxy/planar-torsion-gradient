module

public import Torsion.Proof.PaperGalerkinRitz
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-! # A certified four-mode upper bound for the continuum eigenvalue -/

noncomputable section
open scoped Matrix
namespace Torsion.Galerkin

/-- Integer trial coefficients in frequencies 2, 4, 6 and 8. -/
private def witness : Fin 4 → ℝ := ![100000, -24386, 1191, -220]

private theorem witness_mass :
    witness ⬝ᵥ (ritzMass 4 *ᵥ witness) = 50130769709968 / 3927 := by
  norm_num [witness, ritzMass, oddSectorFrequency, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private theorem witness_energy :
    witness ⬝ᵥ (ritzStiffness 4 *ᵥ witness) = 11193803035 * Real.pi := by
  norm_num [witness, ritzStiffness, oddSectorFrequency, Matrix.diagonal,
    Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- A rational four-mode Rayleigh trial certifies a nine-decimal upper bound
on the continuum eigenvalue appearing in Section 7, Table 1. -/
theorem secondEigenvalue_lt_four_mode_bound : Spectral.secondEigenvalue < 2.754761863 := by
  have h := ritz_rayleigh 4 witness
  rw [witness_mass, witness_energy] at h
  linarith [Real.pi_lt_d20]

end Torsion.Galerkin

module

public import Lean
public import SubmissionStatement
public import Torsion.CanonicalOptimization
public import Torsion.Proof.PaperUniqueness
public import Torsion.Proof.PaperNormalizedFlatSide

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace TorsionSubmission

/-- The concrete claim follows from the original unconditional development;
there are no mathematical proof parameters or additional assumptions. -/
theorem solution : Claim := by
  refine ⟨?_, Torsion.second_exact_value⟩
  intro D
  exact Torsion.DirichletTheory.G_le_second_spectral_bound Torsion.torsionTheory D

/-- Both main theorems, including the classification of every maximizer. -/
theorem paperSolution : Claim ∧ Classification :=
  ⟨solution, Torsion.second_sharp_equality_iff_similarity⟩

/-- Both headline theorems with the conformal, area and midpoint clauses. -/
theorem paperTheorems : (Claim ∧ Classification) ∧ Geometry := by
  refine ⟨paperSolution, ?_⟩
  dsimp only [Geometry]
  open Torsion.Spectral in
    refine ⟨fun z hz => cauchy_conformalAt secondEigenfunction_continuous secondEigenfunction_odd
        secondEigenfunction_zero_exterior secondEigenfunction_pos hz,
      cauchy_injOn_upperHalfPlane secondEigenfunction_continuous secondEigenfunction_odd
        secondEigenfunction_zero_exterior secondEigenfunction_pos,
      ⟨secondCauchyDomain, rfl, secondCauchyDomain_area_spectral⟩, ?_⟩
  obtain ⟨D, U, g, hD, hA, hu, _, hc, hq, _, _, _⟩ := Torsion.second_lipschitz_and_distance_sharp
  refine ⟨D, Torsion.Spectral.normalizedFlatHalfWidth, U, g, hD, hA,
    Torsion.Spectral.normalizedFlatHalfWidth_pos, ?_, hu, ?_, hq⟩
  · rw [hD]
    exact Torsion.Spectral.real_mem_frontier_normalizedImage_iff
  · exact hc.continuous

end TorsionSubmission

#print axioms TorsionSubmission.solution
#print axioms TorsionSubmission.paperSolution
#print axioms TorsionSubmission.paperTheorems

-- Audit this new entry point as well as the original project's Audit.lean.
run_cmd do
  for ax in (← Lean.collectAxioms `TorsionSubmission.paperTheorems) do
    unless [(`propext), (`Classical.choice), (`Quot.sound)].contains ax do
      throwError "Unexpected axiom {ax} in the submission theorem"
  Lean.logInfo "Submission theorem depends only on the permitted axioms."

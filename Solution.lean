module

public import Lean
public import SubmissionStatement
public import Torsion.CanonicalOptimization
public import Torsion.Proof.PaperUniqueness

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

end TorsionSubmission

#print axioms TorsionSubmission.solution
#print axioms TorsionSubmission.paperSolution

-- Audit this new entry point as well as the original project's Audit.lean.
run_cmd do
  for ax in (← Lean.collectAxioms `TorsionSubmission.paperSolution) do
    unless [(`propext), (`Classical.choice), (`Quot.sound)].contains ax do
      throwError "Unexpected axiom {ax} in the submission theorem"
  Lean.logInfo "Submission theorem depends only on the permitted axioms."

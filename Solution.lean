import Lean
import Challenge
import Torsion.CanonicalOptimization

namespace TorsionSubmission

/-- The concrete claim follows from the original unconditional development;
there are no mathematical proof parameters or additional assumptions. -/
theorem solution : Claim := by
  refine ⟨?_, Torsion.second_exact_value⟩
  intro D
  exact Torsion.DirichletTheory.G_le_second_spectral_bound Torsion.torsionTheory D

end TorsionSubmission

#print axioms TorsionSubmission.solution

-- Audit this new entry point as well as the original project's Audit.lean.
run_cmd do
  let env ← Lean.getEnv
  let collect : Lean.CollectAxioms.M Unit := do
    Lean.CollectAxioms.collect `TorsionSubmission.solution
  let (_, state) := ((collect.run env).run {})
  for ax in state.axioms do
    unless [(`propext), (`Classical.choice), (`Quot.sound)].contains ax do
      throwError "Unexpected axiom {ax} in the submission theorem"
  Lean.logInfo "Submission theorem depends only on the permitted axioms."

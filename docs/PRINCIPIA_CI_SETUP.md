# Candidate CI and external claim

These are additive candidate files for the **root of the extracted `torsion-lean` Lake project**. They do not replace or modify any original mathematical source, toolchain, dependency manifest, or audit file. They have not been compiled locally: this workspace has neither Lean nor the cached dependencies installed.

`Challenge.lean` defines `TorsionSubmission.Claim` using the original definitions. It states:

1. The sharp bound on the genuine interior weak-gradient essential supremum for every original nonempty bounded open convex planar domain.
2. The exact area-one supremum in terms of the actual second restricted eigenpair.
3. Attainment by a domain whose carrier is exactly the area-normalized Cauchy image, with area one and the required gradient value.

It imports the constructed second profile and the base definitions, without importing the final universal-bound or optimization modules. There is no assumption of the claim itself and no placeholder proof. `Solution.lean` proves this claim from `Torsion.DirichletTheory.G_le_second_spectral_bound` and `Torsion.second_exact_value`, then checks the proof's complete axiom dependencies against the existing three-axiom allowlist. The source definitions—not a renamed or weakened substitute—determine the statement.

The workflow checks the pinned Lean/mathlib versions, uses the official Lean action to build the original library, runs the unchanged `Audit.lean`, and elaborates both candidate files. `Challenge.olean` is placed in Lake's existing module search path so `Solution.lean` can import it without changing `lakefile.toml`. The original audit covers project theorems; the added audit covers the new submission theorem.

## Principia integration still required

This is a standard GitHub Lean build/audit workflow. Its success alone must not be reported as a Principia comparator pass. No comparator job or comparator result is fabricated here.

The recovered public `PrincipiaMathOrg/PrincipiaTemplate` documentation requires Lean **4.35.0-rc2 or later**, module headers and public visibility in all Lean files, and its bundled Lake comparator. This project's original verified baseline is **Lean 4.19.0**. The current wrapper and ordinary CI deliberately retain that baseline; they have not been compiled or comparator-checked. They do not make the project ready for the modern comparator.

Current Principia integration therefore needs either a separately validated port of the original development and template-shaped wrapper, or an officially supported verifier compatible with the pinned legacy toolchain. Do not silently change the toolchain or report the existing historical audit as validation of a port. The additive wrapper shape can be adapted once a compatible comparison path is established, while preserving the explicit mathematical claim and original development. Uniqueness and full gradient-functional stability remain outside this claim.

The checkout and Lean action revisions are pinned to the immutable commits used
by PrincipiaMathOrg/PrincipiaTemplate at tree
`da848aff2c509e82aae4426a82f50dc525928013`. The original Lean and mathlib pins
remain unchanged. The action settings follow the official documentation:
https://github.com/leanprover/lean-action/blob/main/README.md.

## Repository creation blocker

Principia confirmed the GitHub connection to `fivestarfoxy`, but its automatic
repository creation was refused because `PrincipiaMathOrg` restricts OAuth app
access. The user subsequently created the dedicated public repository
`fivestarfoxy/planar-torsion-gradient` directly in GitHub. This snapshot is
prepared for that repository; the unrelated private repository was left unchanged.
This does not by itself resolve the comparator/toolchain compatibility above.

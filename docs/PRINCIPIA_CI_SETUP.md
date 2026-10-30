# Principia statement/proof interface and verification

## Passing baseline and current port

The original Lean 4.19 baseline at commit `a4fe19c71d4ac5ffbd85fc9d2f013a0c7b1a5e4b` passed its complete build, 3,587-theorem axiom audit, and aggregate submission wrapper in [GitHub run 41132349657](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/runs/41132349657). Both the original audit and the wrapper allow only `propext`, `Classical.choice`, and `Quot.sound`.

This compatibility branch genuinely targets Lean **4.35.0-rc2** and mathlib commit **065356127b1dc0016f66b7283ce0ce2c4055aa55**, with transitive versions pinned in `lake-manifest.json`. The current official Principia template requires this newer toolchain for its bundled Comparator and independent kernels. Porting includes the required `module` headers, public imports, exposed public declarations, and adaptations to changed mathlib APIs. Mathematical statements, definitions, and proof scope are preserved. The passing `main` baseline remains intact while this port is validated.

The port's complete build, recursive axiom audit, and Comparator verification are **pending**. The old successful run is evidence for its recorded commit and compiler; it is not a verification pass for the port.

## Concrete statement and proof

`SubmissionStatement.lean` defines `TorsionSubmission.Claim` using the original convex domains, weak torsion gradient, Euclidean area, spectral constant, and normalized Cauchy image. `Challenge.lean` imports it and advertises `TorsionSubmission.solution : Claim` in the reference environment. Its one deliberate `sorry` is a reference placeholder, outside the proof development. It must never enter `Solution.lean`'s import closure or the theorem audit. The proved `Solution.lean` imports the statement and canonical optimization theorem, and performs its own recursive axiom check. The two same-named theorems belong to separate environments.

The claim covers the universal sharp bound, exact optimal constant, and attainment. It does not claim the manuscript's classical uniqueness classification, full gradient-functional stability, or higher-dimensional and perimeter extensions.

`definition_names` in `comparator.json` is deliberately empty. The official Comparator uses this field for definition **holes** whose bodies may differ; it is not an exact-body comparison list. The concrete `Claim` definition remains fixed and is subject to Comparator's comparison of declarations used in the theorem statement. The permitted axiom list contains only the three axioms named above.

`formalization.yaml` follows the official v0.4 format. It credits Caden Young, identifies the unpublished manuscript, discloses ChatGPT assistance without inventing exact historical model identifiers, and distinguishes baseline verification from the pending port checks. External-wrapper repository metadata is omitted because this repository contains the substantive proof development.

## Ordinary build and audit

The `lean-audit.yml` workflow checks the exact Lean and mathlib pins, builds the full library, runs `Audit.lean`, and builds `SubmissionStatement`, `Challenge`, and `Solution`. The local equivalents are:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
lake build SubmissionStatement Challenge Solution
```

Successful completion is ordinary Lean build and axiom-audit evidence for that checkout. It does not constitute a Comparator pass.

## Sandboxed Comparator and independent kernels

The separate `comparator.yml` workflow follows [PrincipiaTemplate](https://github.com/PrincipiaMathOrg/PrincipiaTemplate) at `da848aff2c509e82aae4426a82f50dc525928013`. It uses a fresh checkout, checks source requirements, installs the pinned toolchain and dependency cache, enables bubblewrap on the disposable Linux runner, and invokes `scripts/verify-comparator.sh`. The solution is not built outside the sandbox before judgment.

For local reproduction, start from a fresh checkout with the pinned toolchain and bubblewrap available:

```sh
python3 scripts/check-lean-sources.py
./scripts/verify-comparator.sh
```

The script obtains Comparator and the independent kernels from the project's actual Lean toolchain. It invokes `lake comparator` with a temporary configuration that registers the bundled `nanoda_bin` and `con-ron` executables. The checked-in configuration cannot provide arbitrary external kernels. The check compares the concrete statement, builds and judges the solution in the sandbox, and replays its proof through Lean's kernel, NanoDa, and con-ron. A successful outcome must come from those checks, not a renamed build job or a historical pass. The workflow retains its Comparator log as an artifact.

Once the port passes, Principia must select its exact repository ref and `.github/workflows/comparator.yml`; the canonical Machine Verification copies can then be explicitly synchronized from that verified ref. Completion of setup alone does not mark the formalization stage verified.

## References

- [PrincipiaTemplate](https://github.com/PrincipiaMathOrg/PrincipiaTemplate)
- [formalization.yaml v0.4 schema](https://github.com/mathlib-initiative/formalization.yaml/blob/main/schema/v0.4.schema.json)
- [Official Comparator documentation](https://github.com/leanprover/comparator/blob/master/README.md)

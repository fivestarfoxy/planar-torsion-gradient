# Principia statement/proof interface

This repository supplies the statement/proof wrappers and metadata below. The original mathematical sources and toolchain pins are unchanged. No Comparator job or pass is supplied.

`SubmissionStatement.lean` preserves the existing concrete `TorsionSubmission.Claim` definition. `Challenge.lean` imports it and advertises the same `TorsionSubmission.solution : Claim` as `Solution.lean` in a separate environment. Its one deliberate `sorry` is a reference placeholder, not part of the proof development; it must never be imported by `Solution.lean` or the original theorem audit. Both same-named theorems must not be imported into one environment. The proved `Solution.lean` imports `Lean`, `SubmissionStatement`, and `Torsion.CanonicalOptimization`, and retains its own recursive axiom check.

`definition_names` is deliberately empty. The official Comparator documentation defines this field as a list of definition **holes** whose bodies may differ; it is not an exact-body comparison list. The proposition `Claim` must remain fixed. Comparator's ordinary check of declarations appearing in theorem statements is the relevant comparison for this concrete definition.

`formalization.yaml` follows the recovered official v0.4 template and schema. It credits Caden Young, identifies the unpublished manuscript, discloses ChatGPT assistance without inventing exact historical model names, and distinguishes the recorded v8 audit from pending ordinary CI and absent Comparator verification. Repository metadata for a thin external wrapper is omitted because this repository contains the substantive development.

Integration status:

- The root `LICENSE` supplies the template's Apache-2.0 terms; the manuscript's separate source license is unknown here.
- Keep verification status current after the ordinary GitHub build/audit completes. Compilation of the proof wrapper does not constitute a Comparator pass.
- Resolve the Lean compatibility blocker. Original Lean 4.19.0 is below Principia's observed preflight minimum of 4.28; the current official template additionally targets Lean 4.35.0-rc2 or later and uses its bundled Comparator/module-visibility setup. A validated toolchain port is required by the current Principia preflight.
- Register additive Lake libraries for `SubmissionStatement`, `Challenge`, and `Solution`, leaving the original `Torsion` default target intact. The ordinary CI can then use `lake build SubmissionStatement Challenge Solution` for the wrappers and the unchanged `lake env lean Audit.lean` for the original development. Such a build is ordinary Lean verification and does not constitute a Comparator pass.

Official references used:

- https://github.com/PrincipiaMathOrg/PrincipiaTemplate
- https://github.com/mathlib-initiative/formalization.yaml/blob/main/schema/v0.4.schema.json
- https://github.com/leanprover/comparator/blob/master/README.md

# Lean 4.35 local verification record

Reproduced 30 October 2026 using the official Lean 4.35.0-rc2 toolchain and
mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
All transitive dependencies are pinned in `lake-manifest.json`.
Project modules were compiled from source against the pinned dependency cache.

The canonical dependency-import check also passed: every imported Mathlib module
exists in the Git tree pinned by the manifest, including on a fresh checkout.

| Check | Result |
| --- | --- |
| `lake build Torsion` | Passed; 4,185 build jobs. |
| `lake env lean Audit.lean` | Passed; full imports for 393 project modules; 4,201 project theorem roots audited. |
| `lake build SubmissionStatement Challenge Solution` | Passed; 4,163 build jobs. |
| Submission theorem axiom dependencies | `propext`, `Classical.choice`, `Quot.sound` only. |

The audit loads every project proof body with `import all` and rejects missing
full imports. Its roots include private/generated declarations and backports
outside the `Torsion` namespace. Imported mathlib axioms are obtained from Lean's
recorded dependency metadata. Compiler-generated declarations differ across
Lean versions, so the current count is not a count of new mathematical results
relative to the historical 3,587-theorem Lean 4.19 audit.

`Challenge.lean` contains the one intentional reference-proof placeholder.
It is excluded from the proof development and the submitted proof's imports.
`Solution.lean` proves the fixed concrete claim and audits its own dependencies.

The exact sharp bound, spectral value, and attainment are covered. Uniqueness
of every maximizer is a separate classical manuscript result. See
[the port note](../docs/LEAN435_PORT.md) for the auxiliary measurability change.

External Comparator verification is a separate exact-commit check using the
pinned official workflow, a bubblewrap sandbox, and the toolchain's Lean,
NanoDa, and con-ron kernels. Its result is reported by the GitHub Actions badge
and Principia; this local record does not substitute for that result.

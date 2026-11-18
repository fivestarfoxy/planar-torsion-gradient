# Planar torsion-gradient optimization in Lean

[![Comparator](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/comparator.yml/badge.svg?branch=codex%2Ffull-paper-formalization)](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/comparator.yml?query=branch%3Acodex%2Ffull-paper-formalization)
[![Build and audit](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/lean-audit.yml/badge.svg?branch=codex%2Ffull-paper-formalization)](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/lean-audit.yml?query=branch%3Acodex%2Ffull-paper-formalization)

Caden Young. Companion development for *An exact spectral construction for the optimal planar torsion gradient*.

For every bounded, nonempty, open convex planar domain, Lean proves the sharp bound for the essential supremum of its weak torsion gradient. It computes the sharp constant from the second eigenfunction of the exterior-zero half-Laplacian and proves that equality holds exactly on the similarities of the constructed domain. A fixed inward boundary quotient realizes the gradient norm even on a nonsmooth convex competitor.

[Paper-to-Lean correspondence](validation/PAPER_COVERAGE.md) · [Submission statements](SubmissionStatement.lean) · [Submission proofs](Solution.lean)

## Build the pinned development

Lean **4.35.0-rc2**; mathlib revision **065356127b1dc0016f66b7283ce0ce2c4055aa55**. The complete dependency set is pinned in `lake-manifest.json`.

```sh
./scripts/verify-clean.sh
```

This checks all pinned dependency source revisions, removes the project's entire `.lake/build`, rebuilds every mathematical module and the aggregate solution, audits the rebuilt declarations, and builds the reference separately. Only external dependency caches are retained. The build-and-audit workflow runs this same procedure on a fresh checkout and preserves its log.

`Torsion.lean` imports the complete development. The source checker compares the filesystem module set with both its build imports and `Audit.lean`'s full imports, rejecting missing, stale, or duplicate entries. `Audit.lean` imports every project proof body with `import all` and checks every project declaration's axiom dependencies, including definitions, private/generated declarations, backports, and unused axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. `Solution.lean` additionally checks the submission theorem's axiom dependencies. Historical build and audit records are listed below.

The separate [Comparator workflow](.github/workflows/comparator.yml) uses the `lake comparator` bundled with the pinned Lean toolchain. It builds the solution in its bubblewrap sandbox, compares it with the reference statement, and replays the proof through Lean's kernel and the bundled independent kernels NanoDa and con-ron. It uses a fresh runner checkout; an ordinary build or axiom-audit pass does not substitute for this check. See [docs/PRINCIPIA_CI_SETUP.md](docs/PRINCIPIA_CI_SETUP.md) for the interface and reproduction instructions.

## Main declarations

| Declaration | Mathematical content |
| --- | --- |
| `TorsionSubmission.paperTheorems` | Both main theorems. Includes conformality, injectivity, the image area, the sharp bound, the flat-side midpoint quotient, and the classification of every equality case. |
| `Torsion.second_sharp_equality_iff_similarity` | Equality holds precisely on translations, positive dilations, and orthogonal images of the spectral domain. |
| `Torsion.DirichletTheory.exists_maximizing_normal_quotient` | Finds a fixed boundary point and an entering inward unit normal where the one-sided quotient of the continuous torsion representative tends to the full gradient norm. |
| `Torsion.Spectral.second_area_one_rigidity_at_maximizing_quotient` | Identifies the domain in the coordinates of the maximizing observation. |
| `Torsion.Spectral.second_marked_area_one_symmDiff_deficit` | Bounds the marked-flux deficit from below in terms of the area of the symmetric difference. |
| `Torsion.Spectral.second_localized_lagrangian_stationary` | Computes the first variation of the physical flux relative to the change in area. |

The reference in `Challenge.lean` uses a single deliberate placeholder for statement comparison. The checked proof in `Solution.lean` imports its own dependencies. The legacy theorem `TorsionSubmission.solution` remains available.

## Verification history

The current workflows are linked at the top of this page. Earlier records cover the [Lean 4.19 build](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/runs/41132349657), the [4.35 port](validation/LEAN435_VERIFICATION.md), the [marked stability extension](validation/MARKED_STABILITY_EXTENSION.md), and the [2 November source audit](validation/AUDIT_20261102.md).

The original Lean 4.19 source and verification evidence remain available at the baseline commit above. The supplied original README is retained in [docs/UPSTREAM_V8_README.md](docs/UPSTREAM_V8_README.md), its original Lake configuration in `docs/UPSTREAM_V8_LAKEFILE.toml`, and historical logs in `validation/`. These records retain their original toolchain context. Earlier comments about conditional interfaces are superseded by the final canonical constructions; inspect the actual definitions and theorem statements.

Source archive v8 SHA-256: `1059841c96aef5d29d8187e53cdf3e69129ee9e3b4bd1ca2d46aab5972185e33`.

[Principia project](https://principia-math.com/projects/bba012475f16aba858c09b39c012a93d).

## License

The repository uses the Apache License 2.0 supplied by the Principia template. Reused components retain their source notices and licenses. The cited manuscript has its own separate rights.

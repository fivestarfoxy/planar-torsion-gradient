# Planar torsion-gradient optimization in Lean

[![Comparator](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/comparator.yml/badge.svg?branch=codex%2Fconcrete-deficit-20261031)](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/comparator.yml?query=branch%3Acodex%2Fconcrete-deficit-20261031)
[![Build and audit](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/lean-audit.yml/badge.svg?branch=codex%2Fconcrete-deficit-20261031)](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/lean-audit.yml?query=branch%3Acodex%2Fconcrete-deficit-20261031)

Caden Young. Companion development for *An exact spectral construction for the optimal planar torsion gradient*.

The formalized core proves the sharp torsion-gradient bound for every original bounded, open, nonempty convex planar domain, the exact spectral value, and attainment by the constructed area-normalized Cauchy image. The weak Dirichlet solution, gradient norm, Euclidean area, restricted half-Laplacian eigenpair, and attaining domain use their original mathematical definitions.

## Verification status

| Development | Status |
| --- | --- |
| Lean 4.19 baseline at `a4fe19c71d4ac5ffbd85fc9d2f013a0c7b1a5e4b` | Full build, 3,587-theorem axiom audit, and submission wrapper passed [GitHub run 41132349657](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/runs/41132349657). |
| Verified Lean 4.35 baseline `cd46d135` | Full build, 4,201-theorem audit across 393 modules, and aggregate submission proof passed; see [baseline record](validation/LEAN435_VERIFICATION.md). |
| Marked-stability extension | Full local build, 4,264-theorem audit across 396 modules, and unchanged submission regression passed; see [extension record](validation/MARKED_STABILITY_EXTENSION.md). |
| Comparator | Exact-commit external status is reported separately; a baseline success is not evidence for a changed tree. |

The Lean 4.19 baseline remains intact on `main`; the Lean 4.35 development is maintained separately. The current port changes module visibility metadata and mathlib API usage while preserving the headline statements and original mathematical objects. One auxiliary convergence lemma makes measurability explicit; its callers already supply those facts. See [the port note](docs/LEAN435_PORT.md). The recorded v8 census of 392 mathematical modules, 52,713 lines, and 3,587 audited theorem declarations describes the historical source, not a new census or audit of this port.

## Build the pinned development

Lean **4.35.0-rc2**; mathlib revision **065356127b1dc0016f66b7283ce0ce2c4055aa55**. The complete dependency set is pinned in `lake-manifest.json`.

```sh
./scripts/verify-clean.sh
```

This checks all pinned dependency source revisions, removes the project's entire `.lake/build`, rebuilds every mathematical module and the aggregate solution, audits the rebuilt declarations, and builds the reference separately. Only external dependency caches are retained. The build-and-audit workflow runs this same procedure on a fresh checkout and preserves its log.

`Torsion.lean` imports the complete development. The source checker compares the filesystem module set with both its build imports and `Audit.lean`'s full imports, rejecting missing, stale, or duplicate entries. `Audit.lean` imports every project proof body with `import all` and checks every project declaration's axiom dependencies, including definitions, private/generated declarations, backports, and unused axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. `Solution.lean` additionally checks the submission theorem's axiom dependencies. See the [2 November source audit](validation/AUDIT_20261102.md) for the manuscript correspondence and repaired coverage gaps.

The separate [Comparator workflow](.github/workflows/comparator.yml) uses the `lake comparator` bundled with the pinned Lean toolchain. It builds the solution in its bubblewrap sandbox, compares it with the reference statement, and replays the proof through Lean's kernel and the bundled independent kernels NanoDa and con-ron. It uses a fresh runner checkout; an ordinary build or axiom-audit pass does not substitute for this check. See [docs/PRINCIPIA_CI_SETUP.md](docs/PRINCIPIA_CI_SETUP.md) for the interface and reproduction instructions.

## Main declarations

- `Torsion.second_exact_value`: exact sharp value and attainment, with no mathematical proof parameters (`Torsion/CanonicalOptimization.lean`).
- `Torsion.DirichletTheory.G_le_second_spectral_bound`: universal bound for arbitrary convex competitors (`Torsion/CanonicalUniversal.lean`).
- `Torsion.Spectral.second_localized_hadamard`: localized marked Hadamard formula (`Torsion/CanonicalHadamard.lean`).
- `Torsion.Spectral.second_marked_area_one_symmDiff_deficit`: concrete `C*/8` geometric deficit against the normalized Cauchy image (`Torsion/CanonicalRadialStability.lean`).
- `Torsion.Spectral.second_marked_area_one_domain_rigidity`: equality of the actual area-one marked domain with that image (same module).
- `Torsion.DirichletTheory.exists_supporting_positive_radial_flux_gt`: an arbitrarily close convex radial outer domain whose marked flux exceeds any strict lower threshold for the full gradient norm (`Torsion/CanonicalGradientStability.lean`).

`SubmissionStatement.lean` defines the concrete aggregate claim using the original objects. `Challenge.lean` states it with the single deliberate reference placeholder used by Comparator. `Solution.lean` imports the statement definitions, never the reference theorem, and proves the same claim from the unconditional development. The reference placeholder is outside the proof development.

## Scope and provenance

The core submission remains the sharp bound, exact value, and attainment.
The marked extension proves the concrete spectral deficit and exact equality
classification within the positive continuous radial class, including the
`C*/8` symmetric-difference bound using genuine planar Lebesgue area and the
actual normalized Cauchy image. Its calibration and Euler identities are
proved inputs, not remaining hypotheses.

A second extension proves that any strict nonnegative lower bound for an
arbitrary convex domain's gradient norm is exceeded by the marked flux of a
convex radial outer domain, in a suitable supporting frame. Both approximation
radii are prescribed in advance. This uses the existing weak boundary-collar
machinery without an external boundary-attainment assumption.

These results do not yet formalize the paper's uniqueness classification for
all convex domains or full gradient-functional shape stability. Those require
the normalized geometric limit and rigidity-of-placement argument. Floating-point
illustrations are not proof inputs. See [the extension record](validation/MARKED_STABILITY_EXTENSION.md).

The original Lean 4.19 source and verification evidence remain available at the baseline commit above. The supplied original README is retained in [docs/UPSTREAM_V8_README.md](docs/UPSTREAM_V8_README.md), its original Lake configuration in `docs/UPSTREAM_V8_LAKEFILE.toml`, and historical logs in `validation/`. These records retain their original toolchain context. Earlier comments about conditional interfaces are superseded by the final canonical constructions; inspect the actual definitions and theorem statements.

Source archive v8 SHA-256: `1059841c96aef5d29d8187e53cdf3e69129ee9e3b4bd1ca2d46aab5972185e33`.

[Principia project](https://principia-math.com/projects/bba012475f16aba858c09b39c012a93d).

## License

The repository uses the Apache License 2.0 supplied by the Principia template. Reused components retain their source notices and licenses. The cited manuscript has its own separate rights.

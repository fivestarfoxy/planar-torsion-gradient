# Planar torsion-gradient optimization in Lean

[![Comparator](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/comparator.yml/badge.svg?branch=principia-lean4.35)](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/comparator.yml?query=branch%3Aprincipia-lean4.35)
[![Build and audit](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/lean-audit.yml/badge.svg?branch=principia-lean4.35)](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/lean-audit.yml?query=branch%3Aprincipia-lean4.35)

Caden Young. Companion development for *An exact spectral construction for the optimal planar torsion gradient*.

The formalized core proves the sharp torsion-gradient bound for every original bounded, open, nonempty convex planar domain, the exact spectral value, and attainment by the constructed area-normalized Cauchy image. The weak Dirichlet solution, gradient norm, Euclidean area, restricted half-Laplacian eigenpair, and attaining domain use their original mathematical definitions.

## Verification status

| Development | Status |
| --- | --- |
| Lean 4.19 baseline at `a4fe19c71d4ac5ffbd85fc9d2f013a0c7b1a5e4b` | Full build, 3,587-theorem axiom audit, and submission wrapper passed [GitHub run 41132349657](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/runs/41132349657). |
| Current Lean 4.35.0-rc2 port | Complete local build, 4,201-theorem audit across 393 project modules, and aggregate submission proof passed; see [verification record](validation/LEAN435_VERIFICATION.md). |
| Principia Comparator for the port | Exact-commit status is reported by the Comparator badge and the Principia project. |

The passing Lean 4.19 baseline remains intact on `main` while the compatibility branch is prepared. The current port changes module visibility metadata and mathlib API usage while preserving the headline statements and original mathematical objects. One auxiliary convergence lemma makes measurability explicit; its callers already supply those facts. See [the port note](docs/LEAN435_PORT.md). The recorded v8 census of 392 mathematical modules, 52,713 lines, and 3,587 audited theorem declarations describes the historical source, not a new census or audit of this port.

## Build the compatibility branch

Lean **4.35.0-rc2**; mathlib revision **065356127b1dc0016f66b7283ce0ce2c4055aa55**. The complete dependency set is pinned in `lake-manifest.json`.

```sh
lake exe cache get
python3 scripts/check-mathlib-imports.py
lake build
lake env lean Audit.lean
lake build SubmissionStatement Challenge Solution
```

`Torsion.lean` imports the complete development. `Audit.lean` explicitly imports every project proof body with `import all`, checks that this coverage is complete, and checks every project theorem's axiom dependencies, allowing only `propext`, `Classical.choice`, and `Quot.sound`. `Solution.lean` additionally checks the submission theorem's axiom dependencies.

The separate [Comparator workflow](.github/workflows/comparator.yml) uses the `lake comparator` bundled with the pinned Lean toolchain. It builds the solution in its bubblewrap sandbox, compares it with the reference statement, and replays the proof through Lean's kernel and the bundled independent kernels NanoDa and con-ron. It uses a fresh runner checkout; an ordinary build or axiom-audit pass does not substitute for this check. See [docs/PRINCIPIA_CI_SETUP.md](docs/PRINCIPIA_CI_SETUP.md) for the interface and reproduction instructions.

## Main declarations

- `Torsion.second_exact_value`: exact sharp value and attainment, with no mathematical proof parameters (`Torsion/CanonicalOptimization.lean`).
- `Torsion.DirichletTheory.G_le_second_spectral_bound`: universal bound for arbitrary convex competitors (`Torsion/CanonicalUniversal.lean`).
- `Torsion.Spectral.second_localized_hadamard`: localized marked Hadamard formula (`Torsion/CanonicalHadamard.lean`).

`SubmissionStatement.lean` defines the concrete aggregate claim using the original objects. `Challenge.lean` states it with the single deliberate reference placeholder used by Comparator. `Solution.lean` imports the statement definitions, never the reference theorem, and proves the same claim from the unconditional development. The reference placeholder is outside the proof development.

## Scope and provenance

The scope remains the sharp bound, exact value, and attainment. The manuscript's classical uniqueness classification is outside the existing Lean final theorem. General deficit identities are formalized with their explicit premises; no separate concrete theorem of full gradient-functional shape stability is claimed. Floating-point illustrations are not proof inputs.

The original Lean 4.19 source and verification evidence remain available at the baseline commit above. The supplied original README is retained in [docs/UPSTREAM_V8_README.md](docs/UPSTREAM_V8_README.md), its original Lake configuration in `docs/UPSTREAM_V8_LAKEFILE.toml`, and historical logs in `validation/`. These records retain their original toolchain context. Earlier comments about conditional interfaces are superseded by the final canonical constructions; inspect the actual definitions and theorem statements.

Source archive v8 SHA-256: `1059841c96aef5d29d8187e53cdf3e69129ee9e3b4bd1ca2d46aab5972185e33`.

[Principia project](https://principia-math.com/projects/bba012475f16aba858c09b39c012a93d).

## License

The repository uses the Apache License 2.0 supplied by the Principia template. Reused components retain their source notices and licenses. The cited manuscript has its own separate rights.

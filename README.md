# Planar torsion-gradient optimization in Lean

[![Lean build and axiom audit](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/lean-audit.yml/badge.svg)](https://github.com/fivestarfoxy/planar-torsion-gradient/actions/workflows/lean-audit.yml)

Caden Young. Companion development for *An exact spectral construction for the optimal planar torsion gradient*.

The formalized core proves the sharp torsion-gradient bound for every original bounded, open, nonempty convex planar domain, the exact spectral value, and attainment by the constructed area-normalized Cauchy image. The weak Dirichlet solution, gradient norm, Euclidean area, restricted half-Laplacian eigenpair, and attaining domain are constructed from their original mathematical definitions.

## Build

Lean **4.19.0**; mathlib revision **c44e0c8ee63ca166450922a373c7409c5d26b00b**, with all dependencies pinned by `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

`Torsion.lean` imports the original development. `Audit.lean` checks every project theorem's axiom dependencies, allowing only `propext`, `Classical.choice`, and `Quot.sound`. The supplied v8 records report 392 mathematical modules, 52,713 source lines, and 3,587 audited theorem declarations. GitHub Actions supplies a separate check of the current repository commit.

## Main declarations

- `Torsion.second_exact_value`: exact sharp value and attainment, with no mathematical proof parameters (`Torsion/CanonicalOptimization.lean`).
- `Torsion.DirichletTheory.G_le_second_spectral_bound`: universal bound for arbitrary convex competitors (`Torsion/CanonicalUniversal.lean`).
- `Torsion.Spectral.second_localized_hadamard`: localized marked Hadamard formula (`Torsion/CanonicalHadamard.lean`).

`Challenge.lean` defines a concrete aggregate claim using the original objects. `Solution.lean` proves that claim from the unconditional development and audits its own axiom dependencies. CI checks these additive entry points after building and auditing the original library. They are preparation for external comparison, not a claim of a Comparator pass.

## Scope and provenance

The manuscript's classical uniqueness classification is outside the existing Lean final theorem. General deficit identities are formalized with their explicit premises; no separate concrete theorem of full gradient-functional shape stability is claimed. Floating-point illustrations are not proof inputs.

The original mathematical sources, toolchain, dependency manifest, and audit are preserved. The supplied original README is retained in [docs/UPSTREAM_V8_README.md](docs/UPSTREAM_V8_README.md), and historical logs remain in `validation/`. Earlier comments about conditional interfaces are superseded by the final canonical constructions; inspect their actual definitions and theorem statements.

Source archive v8 SHA-256: `1059841c96aef5d29d8187e53cdf3e69129ee9e3b4bd1ca2d46aab5972185e33`.

[Principia project](https://principia-math.com/projects/bba012475f16aba858c09b39c012a93d). See [docs/PRINCIPIA_CI_SETUP.md](docs/PRINCIPIA_CI_SETUP.md) for the build/audit workflow and remaining comparator compatibility work. The existing Lean 4.19 baseline has not been silently upgraded to the newer template toolchain.

# Concrete marked stability and supporting outer observations

31 October 2026. Extends the verified Lean 4.35 baseline
`cd46d135100c34a761ad050dadfa96ae1d935df7` without changing the core submission claim.

The canonical calibration and Euler identities now instantiate the existing
continuous-profile deficit theorems. The new statements concern the actual
weak-torsion flux, actual normalized Cauchy image, and planar Lebesgue area.

## New coverage

- `Torsion/RadialSymmetricDifference.lean` proves the geometric comparison
  between symmetric-difference area and the angular L² distance, including
  the area-one squared estimate.
- `Torsion/CanonicalRadialStability.lean` proves normalized and area-one
  deficits, the concrete C*/8 symmetric-difference bound, and exact equality
  in the marked radial class. Calibration and Euler identities are proved
  facts, not remaining assumptions in the endpoint declarations.
- `Torsion/CanonicalGradientStability.lean` proves that every nonnegative
  strict lower threshold for an arbitrary convex domain's weak-gradient
  norm is exceeded by a marked flux in a supporting frame. The positive
  continuous convex radial outer domain contains the framed original and
  lies in its (2r+δ)-thickening, for any prescribed r,δ>0. This uses weak
  boundary collars and assumes no boundary-attainment theorem.

The original `SubmissionStatement.Claim` and `Solution.lean` are unchanged.
Full gradient-functional stability and uniqueness for all convex maximizers
still require the normalized geometric limit and the argument controlling
rigid placements. The new marked rigidity theorem does not assert either.

## Local validation

Using Lean 4.35.0-rc2 and the unchanged pinned dependency manifest:

```sh
lake build
python3 scripts/check-mathlib-imports.py
lake env lean Audit.lean
lake build SubmissionStatement Challenge Solution
```

- Full library build passed: 4,188 jobs.
- Canonical dependency-import guard passed.
- Recursive audit passed: 4,264 theorem roots across all 396 project modules,
  including private and compiler-generated declarations.
- Every audited theorem depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- The unchanged aggregate submission regression passed: 4,163 jobs; its
  theorem has the same three permitted axiom dependencies.
- No admissions or new axiom declarations occur in the added modules.
  The deliberate Challenge reference placeholder remains isolated from
  the submitted proof and development audit.

The local host exposes the current executable through `/proc/self/exe` but
does not resolve Lean's numeric `/proc/<getpid()>/exe` path correctly. A private
`readlink` compatibility shim redirected only that exact same-process lookup
to `/proc/self/exe`; all other calls passed through unchanged. No compiler or
kernel binary modifications were performed. SHA-256 comparisons against the
official release archive matched all nine checked Lean/Lake/kernel/shared-library
files. This host accommodation is not part of the repository or its proofs.

The existing GitHub workflows run in their ordinary Ubuntu environment.
Their exact-commit build/audit and sandboxed Comparator results are separate
evidence; the local checks above do not claim a new three-kernel replay.

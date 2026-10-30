# Lean 4.35 port note

This port updates the project to Lean 4.35.0-rc2 and its matching mathlib APIs.
Most changes are proof syntax, measurability projections, support lemma names,
and normalization of pointwise function operations.

One auxiliary interface changes in
`Torsion/SobolevComposition.lean`: `Torsion.tendsto_eLpNorm_lipschitz_comp`
now takes explicit measurability proofs:

```lean
(huₙ : ∀ n, AEStronglyMeasurable (uₙ n) volume)
(hu : AEStronglyMeasurable u volume)
```

Current mathlib assigns `eLpNorm` the value infinity on functions that are not
a.e. strongly measurable. Convergence of the differences `uₙ - u` alone does
not establish measurability of the nonlinear differences `Ψ ∘ uₙ - Ψ ∘ u`.
The helper therefore uses these proofs and the continuity of the Lipschitz
map to establish measurability before applying the norm estimate.

Both direct callers discharge the new arguments from existing facts:

- `MemH10.comp_smooth_lipschitz` uses continuity of the smooth approximants
  and the original value's `MemLp` proof.
- `MemH10.tendsto_eLpNorm_pos_part` in
  `Torsion/SobolevLatticeContinuity.lean` uses the supplied `MemH10` value
  coordinates for the sequence and its limit.

The mathematical statements and hypotheses of these callers are unchanged.
This adjustment adds no measurability premise to a competitor or domain and
does not weaken the headline Sobolev, PDE, or final optimization statements.

Targeted builds of all 42 Sobolev and Weak modules have succeeded under the
new toolchain. At the time of this note, the complete Lean 4.35 build, audit,
and Principia Comparator verification are still pending. The previously
verified Lean 4.19 baseline is a separate verification result.

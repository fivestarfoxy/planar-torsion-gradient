/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in Torsion/ComplexAnalysis/LICENSE.
Authors: The Tau Ceti contributors

Adapted to Lean/mathlib 4.19 from TauCeti commit
e6b5f42c62ab0484faf5c0e66079de65bcc138a2,
TauCeti/Analysis/Complex/Conformal/Reflection/{Basic,Principle}.lean.
-/
import Torsion.ComplexAxisRemovability
import Torsion.ComplexSchwarzReflectionBasic


/-! Schwarz reflection across the real axis for continuous boundary values. -/
noncomputable section
open Complex Filter Set
open scoped Topology ComplexConjugate

namespace Torsion.ComplexReflection

/-- **Schwarz reflection principle.** A holomorphic function continuous
on the closed upper part of an open conjugation-symmetric domain, and
real-valued on its diameter, has the explicit holomorphic reflection. -/
theorem differentiableOn_schwarzReflection_of_symmetric {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩopen : IsOpen Ω) (hΩ : MapsTo conj Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    DifferentiableOn ℂ (schwarzReflection f) Ω :=
  differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero hΩopen
    (continuousOn_schwarzReflection_of_symmetric hΩ hcont hreal)
    (differentiableOn_schwarzReflection_off_axis hΩopen hΩ hholo)

/-- A holomorphic extension which agrees with the continuous closed upper
branch; this form is convenient when the explicit reflection is hidden. -/
theorem exists_differentiableOn_eqOn_of_symmetric {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩopen : IsOpen Ω) (hΩ : MapsTo conj Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ EqOn F f (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
  refine ⟨schwarzReflection f, differentiableOn_schwarzReflection_of_symmetric hΩopen hΩ
    hcont hholo hreal, ?_⟩
  exact fun z hz => schwarzReflection_of_im_nonneg hz.2

end Torsion.ComplexReflection

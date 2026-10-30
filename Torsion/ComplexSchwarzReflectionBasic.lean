/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in Torsion/ComplexAnalysis/LICENSE.
Authors: The Tau Ceti contributors

Adapted to Lean/mathlib 4.19 from TauCeti commit
e6b5f42c62ab0484faf5c0e66079de65bcc138a2,
TauCeti/Analysis/Complex/Conformal/Reflection/{Basic,Principle}.lean.
-/
import Torsion.ComplexConjugateDerivative
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Complex.ReImTopology

/-! Schwarz reflection across the real axis for continuous boundary values. -/
noncomputable section
open Complex Filter Set
open scoped Topology ComplexConjugate

namespace Torsion.ComplexReflection

/-- Explicit reflection of the closed upper branch across the real axis. -/
def schwarzReflection (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then f z else conj (f (conj z))

@[simp] theorem schwarzReflection_of_im_nonneg {f : ℂ → ℂ} {z : ℂ} (hz : 0 ≤ z.im) :
    schwarzReflection f z = f z := by simp [schwarzReflection, hz]

@[simp] theorem schwarzReflection_of_im_neg {f : ℂ → ℂ} {z : ℂ} (hz : z.im < 0) :
    schwarzReflection f z = conj (f (conj z)) := by simp [schwarzReflection, not_le.mpr hz]

private theorem apply_eq_conj_apply_conj_of_real {f : ℂ → ℂ} {z : ℂ}
    (hz : z.im = 0) (hf : (f z).im = 0) : f z = conj (f (conj z)) := by
  have hc : conj z = z := Complex.conj_eq_iff_im.mpr hz
  rw [hc]
  exact (Complex.conj_eq_iff_im.mpr hf).symm

/-- The reflected function is continuous on a symmetric domain when its
upper branch is continuous and its axis values are real. -/
theorem continuousOn_schwarzReflection_of_symmetric {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩ : MapsTo conj Ω Ω) (hf : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    ContinuousOn (schwarzReflection f) Ω := by
  have hUclosed : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_Ici.preimage continuous_im
  have hlower : ContinuousOn (fun z : ℂ => conj (f (conj z)))
      (Ω ∩ {z : ℂ | z.im ≤ 0}) := by
    have hmaps : MapsTo conj (Ω ∩ {z : ℂ | z.im ≤ 0}) (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
      intro z hz
      exact ⟨hΩ hz.1, by simpa using neg_nonneg.mpr (show z.im ≤ 0 from hz.2)⟩
    simpa only [Function.comp_def, starRingEnd_apply, Pi.star_def] using
      (hf.comp continuous_conj.continuousOn hmaps).star
  change ContinuousOn (fun z : ℂ => if 0 ≤ z.im then f z else conj (f (conj z))) Ω
  refine ContinuousOn.if ?_ ?_ ?_
  · intro z hz
    rw [mem_inter_iff, Complex.frontier_setOf_le_im, mem_setOf_eq] at hz
    exact apply_eq_conj_apply_conj_of_real hz.2 (hreal z hz.1 hz.2)
  · rwa [hUclosed.closure_eq]
  · simp only [not_le]
    rw [Complex.closure_setOf_im_lt]
    exact hlower

/-- The reflected function is holomorphic away from the axis. -/
theorem differentiableOn_schwarzReflection_off_axis {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩopen : IsOpen Ω) (hΩ : MapsTo conj Ω Ω)
    (hf : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im})) :
    DifferentiableOn ℂ (schwarzReflection f) (Ω ∩ {z : ℂ | z.im ≠ 0}) := by
  have hUopen : IsOpen (Ω ∩ {z : ℂ | 0 < z.im}) :=
    hΩopen.inter (isOpen_lt continuous_const continuous_im)
  intro z hz
  rcases lt_or_gt_of_ne hz.2 with hneg | hpos
  · have hc : conj z ∈ Ω ∩ {z : ℂ | 0 < z.im} :=
      ⟨hΩ hz.1, by simpa using neg_pos.mpr hneg⟩
    have hd := hasDerivAt_conj_conj (hf.differentiableAt (hUopen.mem_nhds hc)).hasDerivAt
    have hdz : DifferentiableAt ℂ (fun w : ℂ => conj (f (conj w))) z := by
      simpa using hd.differentiableAt
    apply (hdz.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [(isOpen_lt continuous_im continuous_const).mem_nhds hneg] with w hw
    exact schwarzReflection_of_im_neg hw
  · have hd := hf.differentiableAt (hUopen.mem_nhds ⟨hz.1, hpos⟩)
    apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds hpos] with w hw
    exact schwarzReflection_of_im_nonneg hw.le


end Torsion.ComplexReflection

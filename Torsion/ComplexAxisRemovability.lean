module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in Torsion/ComplexAnalysis/LICENSE.
Authors: The Tau Ceti contributors

Adapted to Lean/mathlib 4.19 from TauCeti commit
e6b5f42c62ab0484faf5c0e66079de65bcc138a2,
TauCeti/Analysis/Complex/Conformal/Removability/Basic.lean.
-/
public import Torsion.ComplexPrimitives

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Continuous holomorphic functions extend across the real axis. -/
noncomputable section
namespace Torsion.ComplexReflection

open Complex Set intervalIntegral MeasureTheory
open scoped Interval

variable {Ω : Set ℂ} {F : ℂ → ℂ}

/-- A rectangle whose open interior avoids the real axis has a vanishing boundary integral for
any function continuous on a domain `Ω` containing the (closed) rectangle and holomorphic on the
part of `Ω` off the real axis. This is the per-rectangle input to Morera's theorem; it is applied
both to axis-avoiding rectangles directly and to the two axis-bounded halves of a straddling
rectangle. -/
private lemma boundaryIntegral_eq_zero_off_axis
    (hcont : ContinuousOn F Ω) (hdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω)
    (haxis : (0 : ℝ) ∉ Set.Ioo (min z.im w.im) (max z.im w.im)) :
    ((∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))) = 0 := by
  refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F z w
    (hcont.mono hsub) (hdiff.mono fun p hp => ?_)
  rw [Complex.mem_reProdIm] at hp
  refine ⟨hsub ?_, ?_⟩
  · rw [Complex.Rectangle, Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [← Icc_min_max]; exact Ioo_subset_Icc_self hp.1
    · rw [← Icc_min_max]; exact Ioo_subset_Icc_self hp.2
  · exact fun h0 => haxis (h0 ▸ hp.2)

/-- A rectangle with a horizontal edge *on* the real axis — one of its imaginary coordinates is `0`
— has a vanishing boundary integral. This is `boundaryIntegral_eq_zero_off_axis` in the case where
the axis meets an edge rather than being avoided outright: an endpoint at `0` still keeps `0` out of
the *open* imaginary interior. It is the form applied to the two axis-bounded halves of a straddling
rectangle. -/
private lemma boundaryIntegral_eq_zero_of_edge_on_axis
    (hcont : ContinuousOn F Ω) (hdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω) (haxis : z.im = 0 ∨ w.im = 0) :
    ((∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))) = 0 := by
  refine boundaryIntegral_eq_zero_off_axis hcont hdiff hsub fun hm => ?_
  -- One imaginary coordinate being `0` puts `0` on the boundary of the imaginary interval, not
  -- inside its open interior `Ioo (min …) (max …)`.
  rcases haxis with h | h <;> rw [h] at hm
  · rcases le_total (0 : ℝ) w.im with hw | hw
    · rw [min_eq_left hw] at hm; exact lt_irrefl (0 : ℝ) hm.1
    · rw [max_eq_left hw] at hm; exact lt_irrefl (0 : ℝ) hm.2
  · rcases le_total z.im 0 with hz | hz
    · rw [max_eq_right hz] at hm; exact lt_irrefl (0 : ℝ) hm.2
    · rw [min_eq_right hz] at hm; exact lt_irrefl (0 : ℝ) hm.1

/-- The integral of `F` along a vertical edge of the rectangle — the edge with fixed real part `a`
— splits at the real axis: the interval integral over `[[z.im, w.im]]` equals the sum of the
integrals over `z.im → 0` and `0 → w.im`, whenever `F` is continuous on a domain `Ω` containing the
rectangle and `0` lies in the imaginary range `[[z.im, w.im]]`. This is the edge-splitting step
used to recombine the two halves of a straddling rectangle. -/
private lemma vertical_edge_split_at_zero
    (hcont : ContinuousOn F Ω) {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω)
    (h0mem : (0 : ℝ) ∈ [[z.im, w.im]]) {a : ℝ} (ha : a ∈ [[z.re, w.re]]) :
    (∫ y : ℝ in z.im..w.im, F (↑a + ↑y * I)) =
      (∫ y : ℝ in z.im..(0 : ℝ), F (↑a + ↑y * I)) +
        ∫ y : ℝ in (0 : ℝ)..w.im, F (↑a + ↑y * I) := by
  -- `F` is continuous along the edge, hence interval-integrable on the parts below and above `0`.
  have contV : ContinuousOn (fun t : ℝ => F (↑a + ↑t * I)) [[z.im, w.im]] :=
    hcont.comp (by fun_prop) fun t ht => hsub (by
      rw [Complex.Rectangle, Complex.mem_reProdIm]
      exact ⟨by simpa using ha, by simpa using ht⟩)
  refine (integral_add_adjacent_intervals ?_ ?_).symm
  · exact (contV.mono (uIcc_subset_uIcc left_mem_uIcc h0mem)).intervalIntegrable
  · exact (contV.mono (uIcc_subset_uIcc h0mem right_mem_uIcc)).intervalIntegrable

/-- A rectangle that *straddles* the real axis — `0` lies strictly inside its imaginary range — has
a vanishing boundary integral: split it at the axis into a lower and an upper half, each an
axis-bounded rectangle handled by `boundaryIntegral_eq_zero_of_edge_on_axis`, and recombine, the
shared axis edge cancelling. Same hypotheses as `boundaryIntegral_eq_zero_off_axis`, but with `0`
in the open imaginary interior instead of outside it. -/
private lemma boundaryIntegral_eq_zero_of_straddling
    (hcont : ContinuousOn F Ω) (hdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω)
    (hstr : (0 : ℝ) ∈ Set.Ioo (min z.im w.im) (max z.im w.im)) :
    ((∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))) = 0 := by
  have h0mem : (0 : ℝ) ∈ [[z.im, w.im]] := by
    rw [← Icc_min_max]; exact Ioo_subset_Icc_self hstr
  -- Split each vertical edge at the axis into its part below and its part above.
  have splitVw := vertical_edge_split_at_zero hcont hsub h0mem right_mem_uIcc
  have splitVz := vertical_edge_split_at_zero hcont hsub h0mem left_mem_uIcc
  -- The lower half `[z, ↑w.re]` and the upper half `[↑z.re, w]`, each bounded by the axis.
  have hsubR1 : Complex.Rectangle z (↑w.re : ℂ) ⊆ Ω := by
    refine fun p hp => hsub ?_
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hp ⊢
    simp only [Complex.ofReal_re, Complex.ofReal_im] at hp
    exact ⟨hp.1, uIcc_subset_uIcc left_mem_uIcc h0mem hp.2⟩
  have hsubR2 : Complex.Rectangle (↑z.re : ℂ) w ⊆ Ω := by
    refine fun p hp => hsub ?_
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hp ⊢
    simp only [Complex.ofReal_re, Complex.ofReal_im] at hp
    exact ⟨hp.1, uIcc_subset_uIcc h0mem right_mem_uIcc hp.2⟩
  have R1 := boundaryIntegral_eq_zero_of_edge_on_axis hcont hdiff hsubR1
    (Or.inr (Complex.ofReal_im w.re))
  have R2 := boundaryIntegral_eq_zero_of_edge_on_axis hcont hdiff hsubR2
    (Or.inl (Complex.ofReal_im z.re))
  simp only [Complex.ofReal_re, Complex.ofReal_im] at R1 R2
  rw [splitVw, splitVz, smul_add, smul_add]
  simp only [smul_eq_mul] at R1 R2 ⊢
  linear_combination R1 + R2

/-- **Painlevé removability of the real axis.** A function continuous on an open set `Ω ⊆ ℂ` and
holomorphic on the part of `Ω` off the real axis is holomorphic on all of `Ω`. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0})) :
    DifferentiableOn ℂ F Ω := by
  refine (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hΩ).mp ⟨?_, hcont⟩
  intro z w hsub
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
  by_cases hstr : (0 : ℝ) ∈ Set.Ioo (min z.im w.im) (max z.im w.im)
  · exact boundaryIntegral_eq_zero_of_straddling hcont hdiff hsub hstr
  · exact boundaryIntegral_eq_zero_off_axis hcont hdiff hsub hstr


end Torsion.ComplexReflection

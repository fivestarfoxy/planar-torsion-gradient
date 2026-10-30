import Torsion.CauchyTransformImageFrontier
import Torsion.CauchyConformalGeometry.BoundaryGeometry
import Mathlib.Analysis.Convex.Topology

/-!
# The actual Cauchy image has a marked flat neighborhood

The free arc is compact and avoids the marked point. The proved frontier
identification therefore excludes every nonreal frontier point near zero.
Connectedness of an upper half-ball and the actual limit at infinity then
force the image to fill that half-ball. No convexity or Jordan theorem is
assumed in this argument.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace Torsion.Spectral

/-- No finite real boundary parameter maps to the marked point. -/
theorem cauchy_boundary_ne_zero {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) (x : ℝ) :
    cauchyExtension φ (x : ℂ) ≠ 0 := by
  intro heq
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hp := cauchy_boundary_re_pos_of_neg hφ hα0 hα1 hodd hzero hpos hx
    simp [heq] at hp
  · have hp := height_pos (hφ.continuous hα0).continuousOn hpos
      (show |(0 : ℝ)| < 1 by norm_num)
    have hi := congrArg Complex.im heq
    simp only [hx, cauchyExtension_ofReal, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
      mul_zero, add_zero, zero_add, Complex.zero_im] at hi
    exact hp.ne' hi
  · have hp := cauchy_boundary_re_neg_of_pos hφ hα0 hα1 hodd hzero hpos hx
    simp [heq] at hp

/-- A positive ball about the marked point misses the complete free arc,
including its two junctions with the real segment. -/
theorem cauchy_freeArc_avoids_ball {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    ∃ r : ℝ, 0 < r ∧ Disjoint (ball (0 : ℂ) r)
      ((fun x : ℝ => cauchyExtension φ (x : ℂ)) '' Icc (-1 : ℝ) 1) := by
  let K : Set ℂ := (fun x : ℝ => cauchyExtension φ (x : ℂ)) '' Icc (-1 : ℝ) 1
  have hcont := (cauchy_boundary_contDiff_one hφ hα0 hα1 hodd hzero).continuous
  have hK : IsCompact K := isCompact_Icc.image hcont
  have h0 : (0 : ℂ) ∈ Kᶜ := by
    rintro ⟨x, _, hx⟩
    exact cauchy_boundary_ne_zero hφ hα0 hα1 hodd hzero hpos x hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hK.isClosed.isOpen_compl.mem_nhds h0)
  exact ⟨r, hr, disjoint_left.2 (fun _ hp hKp => hball hp hKp)⟩

/-- Every actual frontier point sufficiently close to zero is real. -/
theorem frontier_cauchyImage_real_near_zero {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ frontier (cauchyImage φ), z ∈ ball 0 r → z.im = 0 := by
  obtain ⟨r, hr, hd⟩ := cauchy_freeArc_avoids_ball hφ hα0 hα1 hodd hzero hpos
  refine ⟨r, hr, ?_⟩
  intro z hz hball
  rw [frontier_cauchyImage_eq (hφ.continuous hα0) hodd hzero hpos] at hz
  rcases hz with ⟨x, rfl⟩ | hz
  · have hx : x ∉ Icc (-1 : ℝ) 1 := by
      intro hx
      exact disjoint_left.1 hd hball ⟨x, hx, rfl⟩
    have habs : 1 ≤ |x| := by
      by_contra! h
      exact hx ⟨(abs_lt.1 h).1.le, (abs_lt.1 h).2.le⟩
    simp [cauchyExtension_ofReal, height_zero_of_one_le_abs φ habs]
  · simpa only [mem_singleton_iff.1 hz] using Complex.zero_im

/-- The image fills an entire upper half-ball near the actual marked point.
This is the flat-neighborhood property, proved directly for the Cauchy image. -/
theorem cauchyImage_flat_neighborhood {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    ∃ r : ℝ, 0 < r ∧ cauchyImage φ ∩ ball 0 r = upperHalfPlane ∩ ball 0 r := by
  have hc := hφ.continuous hα0
  have hopen := cauchyImage_isOpen hc hodd hzero hpos
  have hsub : cauchyImage φ ⊆ upperHalfPlane := by
    rintro w ⟨z, hz, rfl⟩
    exact cauchy_im_pos hc.continuousOn hpos hz
  obtain ⟨r, hr, hreal⟩ := frontier_cauchyImage_real_near_zero hφ hα0 hα1 hodd hzero hpos
  have hpre : IsPreconnected (upperHalfPlane ∩ ball (0 : ℂ) r) :=
    ((convex_halfSpace_im_gt (0 : ℝ)).inter (convex_ball 0 r)).isPreconnected
  have hmeet : ((upperHalfPlane ∩ ball (0 : ℂ) r) ∩ cauchyImage φ).Nonempty := by
    have h0 := frontier_subset_closure (zero_mem_frontier_cauchyImage hc hodd hzero hpos)
    obtain ⟨z, hzball, hz⟩ := mem_closure_iff.1 h0 (ball 0 r) isOpen_ball (mem_ball_self hr)
    exact ⟨z, ⟨hsub hz, hzball⟩, hz⟩
  have hall : upperHalfPlane ∩ ball (0 : ℂ) r ⊆ cauchyImage φ := by
    apply hpre.subset_of_closure_inter_subset hopen hmeet
    rintro z ⟨hzcl, hzupper, hzball⟩
    by_contra hz
    have hzfront : z ∈ frontier (cauchyImage φ) := by
      rw [hopen.frontier_eq]
      exact ⟨hzcl, hz⟩
    exact (ne_of_gt hzupper) (hreal z hzfront hzball)
  exact ⟨r, hr, Subset.antisymm (inter_subset_inter_left _ hsub)
    (fun _ hz => ⟨hall hz, hz.2⟩)⟩

/-- The actual Cauchy image satisfies every clause of the original marked
geometry definition, without assuming its convexity or a flat side. -/
theorem cauchyImage_isMarked {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    IsMarked (cauchyImage φ) := by
  have hc := hφ.continuous hα0
  refine ⟨cauchyImage_isOpen hc hodd hzero hpos,
    cauchy_image_isBounded hc hodd hzero, ?_,
    cauchyImage_flat_neighborhood hφ hα0 hα1 hodd hzero hpos⟩
  rintro w ⟨z, hz, rfl⟩
  exact cauchy_im_pos hc.continuousOn hpos hz

end Torsion.Spectral

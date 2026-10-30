import Torsion.CauchyConformalGeometry.BoundaryJunctionHolder
import Torsion.CauchyConformalGeometry.FlatSegment

/-!
# The joined charts cover actual frontier neighborhoods of both junctions

Every free-arc point is already in the chart. A flat-side point within
bδ of a junction is covered by the adjacent linear continuation of length
δ. Thus these regular Hölder charts describe actual boundary neighborhoods.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The joined chart covers an actual relative-frontier neighborhood of
the right junction, with the explicit physical radius bδ. -/
theorem cauchyJoinedBoundary_frontier_near_right_subset {a b δ : ℝ}
    {φ : ℝ → ℝ} {C α : ℝ≥0} (hb : 0 < b) (hδ : 0 < δ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    frontier (cauchyImage φ) ∩ ball (cauchyExtension φ (1 : ℂ)) (b * δ) ⊆
      cauchyJoinedBoundary φ '' Icc (-1 - δ) (1 + δ) := by
  rintro w ⟨hw, hwball⟩
  rw [frontier_cauchyImage_freeArc_union_segment hφ hα0 hα1 hodd hzero hpos] at hw
  rcases hw with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · refine ⟨s, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    exact cauchyJoinedBoundary_eq_on_interval hφ hα0 hα1 hodd hzero hs
  · let R := (cauchyExtension φ (1 : ℂ)).re
    have hep : cauchyExtension φ (1 : ℂ) = (R : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using (cauchy_boundary_endpoints hφ hα0 hα1 hodd hzero hpos).2.1
    have hd : 0 ≤ s - R := sub_nonneg.2 hs.1
    have hdist : s - R < b * δ := by
      rw [hep] at hwball
      simpa only [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd] using hwball
    let t : ℝ := 1 + (s - R) / b
    have ht : 1 ≤ t := by dsimp [t]; exact le_add_of_nonneg_right (div_nonneg hd hb.le)
    have htδ : t ≤ 1 + δ := by
      dsimp [t]
      have h : (s - R) / b < δ := (div_lt_iff₀ hb).2 (by nlinarith)
      linarith
    refine ⟨t, ⟨by linarith, htδ⟩, ?_⟩
    rw [cauchyJoinedBoundary_eq_right hφ hα0 hα1 hodd hzero hlinear ht, hep]
    dsimp [t]
    have halg : b * (1 + (s - R) / b - 1) = s - R := by
      field_simp
    rw [halg, ← Complex.ofReal_add]
    congr 1
    ring

/-- The corresponding explicit frontier-neighborhood coverage at the
left junction. -/
theorem cauchyJoinedBoundary_frontier_near_left_subset {a b δ : ℝ}
    {φ : ℝ → ℝ} {C α : ℝ≥0} (hb : 0 < b) (hδ : 0 < δ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    frontier (cauchyImage φ) ∩ ball (cauchyExtension φ (-1 : ℂ)) (b * δ) ⊆
      cauchyJoinedBoundary φ '' Icc (-1 - δ) (1 + δ) := by
  rintro w ⟨hw, hwball⟩
  rw [frontier_cauchyImage_freeArc_union_segment hφ hα0 hα1 hodd hzero hpos] at hw
  rcases hw with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · refine ⟨s, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    exact cauchyJoinedBoundary_eq_on_interval hφ hα0 hα1 hodd hzero hs
  · let L := (cauchyExtension φ (-1 : ℂ)).re
    have hep : cauchyExtension φ (-1 : ℂ) = (L : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using (cauchy_boundary_endpoints hφ hα0 hα1 hodd hzero hpos).1
    have hd : s - L ≤ 0 := sub_nonpos.2 hs.2
    have hdist : -(b * δ) < s - L := by
      rw [hep] at hwball
      have h : -(s - L) < b * δ := by
        simpa only [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hd] using hwball
      linarith
    let t : ℝ := -1 + (s - L) / b
    have ht : t ≤ -1 := by dsimp [t]; exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hd hb.le)
    have htδ : -1 - δ ≤ t := by
      dsimp [t]
      have h : -δ < (s - L) / b := (lt_div_iff₀ hb).2 (by nlinarith)
      linarith
    refine ⟨t, ⟨htδ, by linarith⟩, ?_⟩
    rw [cauchyJoinedBoundary_eq_left hφ hα0 hα1 hodd hzero hlinear ht, hep]
    dsimp [t]
    have halg : b * (-1 + (s - L) / b + 1) = s - L := by
      field_simp
    rw [halg, ← Complex.ofReal_add]
    congr 1
    ring

/-- Actual spectral data construct a common positive radius at which the
joined chart covers both actual boundary junction neighborhoods. -/
theorem cauchyJoinedBoundary_covers_junctions {a b δ : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hδ : 0 < δ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    ∃ ρ : ℝ, 0 < ρ ∧
      frontier (cauchyImage φ) ∩ ball (cauchyExtension φ (-1 : ℂ)) ρ ⊆
        cauchyJoinedBoundary φ '' Icc (-1 - δ) (1 + δ) ∧
      frontier (cauchyImage φ) ∩ ball (cauchyExtension φ (1 : ℂ)) ρ ⊆
        cauchyJoinedBoundary φ '' Icc (-1 - δ) (1 + δ) := by
  have hb := (coefficient_pos_and_unique_velocity_zero_of_holder_boundary_equation
    ha hφ hα0 hα1 hodd hzero hpos hlinear).1
  exact ⟨b * δ, mul_pos hb hδ,
    cauchyJoinedBoundary_frontier_near_left_subset hb hδ hφ hα0 hα1 hodd hzero hpos hlinear,
    cauchyJoinedBoundary_frontier_near_right_subset hb hδ hφ hα0 hα1 hodd hzero hpos hlinear⟩

end Torsion.Spectral

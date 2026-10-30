module

public import Torsion.CauchyConformalGeometry.BoundaryJunctionHolder
public import Torsion.CauchyConformalGeometry.FlatSegment
public import Torsion.CauchyConformalGeometry.BoundaryJunctionCoverage

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The joined charts parametrize the actual physical frontier

The regular C¹,α continuation constructed in `BoundaryJunctionHolder` is
shown here to be an embedded parametrization of the actual free arc and
its two adjacent flat pieces. Its image contains relative frontier
neighborhoods of both junctions, so its regularity is physical boundary
regularity rather than merely regularity of an auxiliary curve.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The joined chart retains exactly the actual height function. -/
theorem cauchyJoinedBoundary_im_eq_height {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) (t : ℝ) :
    (cauchyJoinedBoundary φ t).im = height φ t := by
  have hi (r : ℝ) : (cauchyExtension φ (r : ℂ)).im = height φ r := by
    simp [cauchyExtension_ofReal]
  by_cases ht : t ∈ Icc (-1 : ℝ) 1
  · rw [cauchyJoinedBoundary_eq_on_interval hφ hα0 hα1 hodd hzero ht]
    simp [cauchyExtension_ofReal]
  · have hy := height_zero_of_one_le_abs φ (show 1 ≤ |t| from by
      by_contra! h; exact ht (abs_le.1 h.le))
    rcases le_or_gt t (-1) with hl | hl
    · rw [cauchyJoinedBoundary_eq_left hφ hα0 hα1 hodd hzero hlinear hl, hy]
      have hz : (cauchyExtension φ (-1 : ℂ)).im = 0 := by
        simpa using (hi (-1)).trans
            (height_zero_of_one_le_abs φ (by norm_num : (1 : ℝ) ≤ |(-1 : ℝ)|))
      simp only [Complex.add_im, Complex.ofReal_im, add_zero, hz]
    · have hr : 1 ≤ t := le_of_not_gt (fun h => ht ⟨hl.le, h.le⟩)
      rw [cauchyJoinedBoundary_eq_right hφ hα0 hα1 hodd hzero hlinear hr, hy]
      have hz : (cauchyExtension φ (1 : ℂ)).im = 0 := by
        simpa using (hi 1).trans
            (height_zero_of_one_le_abs φ (by norm_num : (1 : ℝ) ≤ |(1 : ℝ)|))
      simp only [Complex.add_im, Complex.ofReal_im, add_zero, hz]

/-- The actual joined chart is injective on every sufficiently short
continuation of its two flat ends. The quantitative conditions simply keep
the two ends on opposite sides of the marked origin. -/
theorem cauchyJoinedBoundary_injOn {a b δ : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hb : 0 < b)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hleft : b * δ < (cauchyExtension φ (-1 : ℂ)).re)
    (hright : b * δ < -(cauchyExtension φ (1 : ℂ)).re) :
    InjOn (cauchyJoinedBoundary φ) (Icc (-1 - δ) (1 + δ)) := by
  have hleftsign (t : ℝ) (ht : t ∈ Icc (-1 - δ) (1 + δ)) (hl : t ≤ -1) :
      0 < (cauchyJoinedBoundary φ t).re := by
    rw [cauchyJoinedBoundary_eq_left hφ hα0 hα1 hodd hzero hlinear hl]
    simp only [Complex.add_re, Complex.ofReal_re]
    nlinarith [mul_nonneg hb.le (sub_nonneg.2 ht.1)]
  have hrightsign (t : ℝ) (ht : t ∈ Icc (-1 - δ) (1 + δ)) (hr : 1 ≤ t) :
      (cauchyJoinedBoundary φ t).re < 0 := by
    rw [cauchyJoinedBoundary_eq_right hφ hα0 hα1 hodd hzero hlinear hr]
    simp only [Complex.add_re, Complex.ofReal_re]
    nlinarith [mul_nonneg hb.le (sub_nonneg.2 ht.2)]
  intro x hx y hy hxy
  have hheight : height φ x = height φ y := by
    simpa only [cauchyJoinedBoundary_im_eq_height hφ hα0 hα1 hodd hzero hlinear] using
      congrArg Complex.im hxy
  have inside_eq (u v : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) (hv : v ∉ Ioo (-1 : ℝ) 1) :
      height φ u ≠ height φ v := by
    have hp := height_pos (hφ.continuous hα0).continuousOn hpos (abs_lt.2 hu)
    have hz := height_zero_of_one_le_abs φ (show 1 ≤ |v| from by
      by_contra! h; exact hv (abs_lt.1 h))
    rw [hz]
    exact hp.ne'
  by_cases hxi : x ∈ Ioo (-1 : ℝ) 1
  · have hyi : y ∈ Ioo (-1 : ℝ) 1 := by
      by_contra h
      exact inside_eq x y hxi h hheight
    apply cauchy_boundary_injOn_interval hφ hα0 hα1 hodd hzero hpos
      (Ioo_subset_Icc_self hxi) (Ioo_subset_Icc_self hyi)
    simpa only [cauchyJoinedBoundary_eq_on_interval hφ hα0 hα1 hodd hzero
      (Ioo_subset_Icc_self hxi), cauchyJoinedBoundary_eq_on_interval hφ hα0 hα1 hodd hzero
      (Ioo_subset_Icc_self hyi)] using hxy
  have hyi : y ∉ Ioo (-1 : ℝ) 1 := by
    intro h
    exact inside_eq y x h hxi hheight.symm
  have hxo : x ≤ -1 ∨ 1 ≤ x := by
    simpa only [mem_Ioo, not_and_or, not_lt] using hxi
  have hyo : y ≤ -1 ∨ 1 ≤ y := by
    simpa only [mem_Ioo, not_and_or, not_lt] using hyi
  rcases hxo with hxl | hxr <;> rcases hyo with hyl | hyr
  · have hre := congrArg Complex.re hxy
    rw [cauchyJoinedBoundary_eq_left hφ hα0 hα1 hodd hzero hlinear hxl,
      cauchyJoinedBoundary_eq_left hφ hα0 hα1 hodd hzero hlinear hyl] at hre
    simp only [Complex.add_re, Complex.ofReal_re] at hre
    have hm : b * (x - y) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hb.ne')
  · have h1 := hleftsign x hx hxl
    have h2 := hrightsign y hy hyr
    rw [hxy] at h1
    linarith
  · have h1 := hrightsign x hx hxr
    have h2 := hleftsign y hy hyl
    rw [hxy] at h1
    linarith
  · have hre := congrArg Complex.re hxy
    rw [cauchyJoinedBoundary_eq_right hφ hα0 hα1 hodd hzero hlinear hxr,
      cauchyJoinedBoundary_eq_right hφ hα0 hα1 hodd hzero hlinear hyr] at hre
    simp only [Complex.add_re, Complex.ofReal_re] at hre
    have hm : b * (x - y) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hb.ne')

/-- Small joined continuations lie on the actual physical frontier. -/
theorem cauchyJoinedBoundary_image_subset_frontier
    {a b δ : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hb : 0 < b)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hright : b * δ < -(cauchyExtension φ (1 : ℂ)).re) :
    cauchyJoinedBoundary φ '' Icc (-1 - δ) (1 + δ) ⊆ frontier (cauchyImage φ) := by
  have hep := cauchy_boundary_endpoints hφ hα0 hα1 hodd hzero hpos
  rw [frontier_cauchyImage_freeArc_union_segment hφ hα0 hα1 hodd hzero hpos]
  rintro w ⟨t, ht, rfl⟩
  by_cases hti : t ∈ Icc (-1 : ℝ) 1
  · exact Or.inl ⟨t, hti, (cauchyJoinedBoundary_eq_on_interval hφ hα0 hα1 hodd hzero hti).symm⟩
  rcases le_or_gt t (-1) with hl | hl
  · rw [cauchyJoinedBoundary_eq_left hφ hα0 hα1 hodd hzero hlinear hl]
    right
    refine ⟨(cauchyExtension φ (-1 : ℂ)).re + b * (t + 1), ⟨?_, ?_⟩, ?_⟩
    · nlinarith [mul_nonneg hb.le (sub_nonneg.2 ht.1), hep.2.2.2]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hb.le (by linarith : t + 1 ≤ 0)]
    · apply Complex.ext <;> simp [hep.1]
  · have hr : 1 ≤ t := le_of_not_gt (fun h => hti ⟨hl.le, h.le⟩)
    rw [cauchyJoinedBoundary_eq_right hφ hα0 hα1 hodd hzero hlinear hr]
    right
    refine ⟨(cauchyExtension φ (1 : ℂ)).re + b * (t - 1), ⟨?_, ?_⟩, ?_⟩
    · nlinarith [mul_nonneg hb.le (by linarith : 0 ≤ t - 1)]
    · nlinarith [mul_nonneg hb.le (sub_nonneg.2 ht.2), hep.2.2.1]
    · apply Complex.ext <;> simp [hep.2.1]

/-- The compact joined parametrization is an actual closed embedding. -/
theorem cauchyJoinedBoundary_isClosedEmbedding
    {a b δ : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hb : 0 < b)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hleft : b * δ < (cauchyExtension φ (-1 : ℂ)).re)
    (hright : b * δ < -(cauchyExtension φ (1 : ℂ)).re) :
    Topology.IsClosedEmbedding (fun t : Icc (-1 - δ) (1 + δ) =>
      cauchyJoinedBoundary φ t) := by
  have hc : Continuous (fun t : Icc (-1 - δ) (1 + δ) => cauchyJoinedBoundary φ t) :=
    (cauchyJoinedBoundary_contDiff_one hφ hα0 hzero).continuous.comp continuous_subtype_val
  apply hc.isClosedEmbedding
  intro t s hts
  exact Subtype.ext (cauchyJoinedBoundary_injOn hb hφ hα0 hα1 hodd hzero hpos hlinear
    hleft hright t.property s.property hts)

/-- There are genuine embedded physical boundary charts through both
junctions. Positivity of the endpoint tangent is derived from the original
linear Hilbert equation and its proved moment identity. -/
theorem exists_cauchyJoinedBoundary_embedded_frontier_chart
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    ∃ δ : ℝ, 0 < δ ∧
      Topology.IsClosedEmbedding (fun t : Icc (-1 - δ) (1 + δ) => cauchyJoinedBoundary φ t) ∧
      cauchyJoinedBoundary φ '' Icc (-1 - δ) (1 + δ) ⊆ frontier (cauchyImage φ) := by
  have hb := (coefficient_pos_and_unique_velocity_zero_of_holder_boundary_equation
    ha hφ hα0 hα1 hodd hzero hpos hlinear).1
  have hep := cauchy_boundary_endpoints hφ hα0 hα1 hodd hzero hpos
  let m := min (cauchyExtension φ (-1 : ℂ)).re (-(cauchyExtension φ (1 : ℂ)).re)
  have hm : 0 < m := lt_min hep.2.2.1 (neg_pos.2 hep.2.2.2)
  let δ : ℝ := m / (2 * b)
  have hδ : 0 < δ := div_pos hm (by positivity)
  have hprod : b * δ = m / 2 := by dsimp [δ]; field_simp; ring
  have hleft : b * δ < (cauchyExtension φ (-1 : ℂ)).re := by
    rw [hprod]
    exact (half_lt_self hm).trans_le (min_le_left _ _)
  have hright : b * δ < -(cauchyExtension φ (1 : ℂ)).re := by
    rw [hprod]
    exact (half_lt_self hm).trans_le (min_le_right _ _)
  exact ⟨δ, hδ,
    cauchyJoinedBoundary_isClosedEmbedding hb hφ hα0 hα1 hodd hzero hpos hlinear hleft hright,
    cauchyJoinedBoundary_image_subset_frontier hb hφ hα0 hα1 hodd hzero hpos hlinear hright⟩

/-- Regular C¹,α embedded charts really parametrize relative neighborhoods
of both actual physical junctions. In particular the Hölder tangent is not
merely an auxiliary extension off the boundary. -/
theorem cauchyJoinedBoundary_regular_frontier_charts
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      Topology.IsClosedEmbedding (fun t : Icc (-1 - δ) (1 + δ) => cauchyJoinedBoundary φ t) ∧
      cauchyJoinedBoundary φ '' Icc (-1 - δ) (1 + δ) ⊆ frontier (cauchyImage φ) ∧
      frontier (cauchyImage φ) ∩ Metric.ball (cauchyExtension φ (-1 : ℂ)) ρ ⊆
        cauchyJoinedBoundary φ '' Icc (-1 - δ) (1 + δ) ∧
      frontier (cauchyImage φ) ∩ Metric.ball (cauchyExtension φ (1 : ℂ)) ρ ⊆
        cauchyJoinedBoundary φ '' Icc (-1 - δ) (1 + δ) ∧
      ContDiff ℝ 1 (cauchyJoinedBoundary φ) ∧
      (∃ K : ℝ≥0, HolderWith K α (deriv (cauchyJoinedBoundary φ))) ∧
      ∀ t : ℝ, deriv (cauchyJoinedBoundary φ) t ≠ 0 := by
  obtain ⟨δ, hδ, hemb, hinto⟩ :=
    exists_cauchyJoinedBoundary_embedded_frontier_chart ha hφ hα0 hα1 hodd hzero hpos hlinear
  obtain ⟨ρ, hρ, hleft, hright⟩ :=
    cauchyJoinedBoundary_covers_junctions ha hδ hφ hα0 hα1 hodd hzero hpos hlinear
  exact ⟨δ, ρ, hδ, hρ, hemb, hinto, hleft, hright,
    cauchyJoinedBoundary_contDiff_one hφ hα0 hzero,
    cauchyJoinedBoundary_deriv_holder hφ hα0 hα1 hodd hzero hlinear,
    cauchyJoinedBoundary_deriv_ne_zero ha hφ hα0 hα1 hodd hzero hpos hlinear⟩

end Torsion.Spectral

import Torsion.CompactLocalBounds
import Torsion.CauchyFreeArcGradient
import Torsion.CauchyConformalGeometry.FlatSegment
import Torsion.PhysicalCauchySobolev

/-!
# Finite physical convection energy for actual compact displacements

The compact support of the physical displacement lies strictly above the
flat side. Its intersection with the image closure therefore meets only
the interior and open free arc. The actual local gradient extensions give
a genuine uniform bound on convection and its classical gradient. This
proves all finite Lᵖ bounds, including the H¹ norms needed for the material
correction, without assuming regularity at a junction.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion.Spectral

theorem IsRestrictedEigenfunction.cauchyConvection_exists_bound
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVU : tsupport V ⊆ upperHalfPlane) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ cauchyImage φ,
      ‖inner (𝕜 := ℝ) (V w) (gradient (physicalCandidate φ) w)‖ +
        ‖gradient (fun z => inner (𝕜 := ℝ) (V z) (gradient (physicalCandidate φ) z)) w‖ ≤ B := by
  have hc := hφ.continuous hα0
  have hD := cauchyImage_isOpen hc hodd hzero hpos
  have hG := contDiffOn_gradient_of_isOpen (physicalCandidate_contDiffOn hc hodd hzero hpos) hD
  apply exists_bound_convection_of_local_extensions hD hV hVc
  intro w hw
  by_cases hwD : w ∈ cauchyImage φ
  · exact ⟨gradient (physicalCandidate φ), (hG w hwD).contDiffAt (hD.mem_nhds hwD),
      Filter.EventuallyEq.rfl⟩
  · have hwF : w ∈ frontier (cauchyImage φ) := by
      rw [hD.frontier_eq]
      exact ⟨hw.1, hwD⟩
    rw [frontier_cauchyImage_freeArc_union_segment hφ hα0 hα1 hodd hzero hpos] at hwF
    rcases hwF with ⟨t, _ht, rfl⟩ | ⟨s, _hs, rfl⟩
    · have him : 0 < (cauchyExtension φ (t : Plane)).im := hVU hw.2
      have ht : t ∈ Ioo (-1 : ℝ) 1 := by
        apply abs_lt.mp
        by_contra hn
        have hY := height_zero_of_one_le_abs φ (le_of_not_gt hn)
        have hh : (cauchyExtension φ (t : Plane)).im = 0 := by
          simp [cauchyExtension_ofReal, hY]
        linarith
      exact hEig.exists_smooth_gradient_at_freeArc ha hφ hα0 hα1 hodd hzero hpos hlinear ht
    · have him : 0 < (s : Plane).im := hVU hw.2
      simp at him

/-- The actual convective value belongs to every Lᵖ on the physical image,
including p=2 and p=∞, for a compact smooth displacement above the flat side. -/
theorem IsRestrictedEigenfunction.cauchyConvection_memLp
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0} {p : ℝ≥0∞}
    (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVU : tsupport V ⊆ upperHalfPlane) :
    MemLp (fun w => inner (𝕜 := ℝ) (V w) (gradient (physicalCandidate φ) w))
      p (volume.restrict (cauchyImage φ)) := by
  have hc := hφ.continuous hα0
  have hD := cauchyImage_isOpen hc hodd hzero hpos
  have hDb := cauchy_image_isBounded hc hodd hzero
  letI : IsFiniteMeasure (volume.restrict (cauchyImage φ)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hDb.measure_lt_top⟩
  have hG := contDiffOn_gradient_of_isOpen (physicalCandidate_contDiffOn hc hodd hzero hpos) hD
  have hconv := hV.contDiffOn.inner ℝ hG
  obtain ⟨B, _, hB⟩ := hEig.cauchyConvection_exists_bound ha hφ hα0 hα1 hodd hzero hpos hlinear
    hV hVc hVU
  apply MemLp.of_bound (hconv.continuousOn.aestronglyMeasurable hD.measurableSet) B
  filter_upwards [ae_restrict_mem hD.measurableSet] with w hw
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hB w hw)

/-- The actual classical convective gradient has every physical Lᵖ bound.
In particular the finite gradient energy is a proved conclusion, not a
boundary-regularity certificate supplied to the shape argument. -/
theorem IsRestrictedEigenfunction.cauchyConvection_gradient_memLp
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0} {p : ℝ≥0∞}
    (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVU : tsupport V ⊆ upperHalfPlane) :
    MemLp (gradient (fun w => inner (𝕜 := ℝ) (V w) (gradient (physicalCandidate φ) w)))
      p (volume.restrict (cauchyImage φ)) := by
  have hc := hφ.continuous hα0
  have hD := cauchyImage_isOpen hc hodd hzero hpos
  have hDb := cauchy_image_isBounded hc hodd hzero
  letI : IsFiniteMeasure (volume.restrict (cauchyImage φ)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hDb.measure_lt_top⟩
  have hG := contDiffOn_gradient_of_isOpen (physicalCandidate_contDiffOn hc hodd hzero hpos) hD
  have hconv := hV.contDiffOn.inner ℝ hG
  have hgrad := contDiffOn_gradient_of_isOpen hconv hD
  obtain ⟨B, _, hB⟩ := hEig.cauchyConvection_exists_bound ha hφ hα0 hα1 hodd hzero hpos hlinear
    hV hVc hVU
  apply MemLp.of_bound (hgrad.continuousOn.aestronglyMeasurable hD.measurableSet) B
  filter_upwards [ae_restrict_mem hD.measurableSet] with w hw
  exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hB w hw)

end Torsion.Spectral

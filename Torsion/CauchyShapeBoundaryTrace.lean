module

public import Torsion.CauchyShapeBoundaryData
public import Torsion.PhysicalCauchyHarmonicBoundary
public import Torsion.PhysicalCauchyHarmonicLp

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The actual zero boundary trace of convection plus its harmonic lift -/

noncomputable section
open Set Filter
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral

theorem gradient_physicalCandidate_tendsto_at_marked
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b) :
    Tendsto (gradient (physicalCandidate φ)) (𝓝[cauchyImage φ] 0)
      (𝓝 (((b / a : ℝ) : Plane) * Complex.I)) := by
  have hH : ∀ᶠ w in 𝓝[cauchyImage φ] 0, cauchyInverse φ w ∈ upperHalfPlane := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact cauchyInverse_mem hw
  have h := gradient_physicalCandidate_cauchy_tendsto_at_infinity ha hφ hα0 hα1
    hodd hzero hpos hlinear (cauchyInverse_norm_tendsto_at_marked hφ hα0 hα1 hodd hzero hpos) hH
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [cauchy_cauchyInverse hw]

theorem negative_convection_boundary_tendsto
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {V : Plane → Plane} (hV : Continuous V) (hVU : tsupport V ⊆ upperHalfPlane) (t : ℝ) :
    Tendsto (fun w => -inner (𝕜 := ℝ) (V w) (gradient (physicalCandidate φ) w))
      (𝓝[cauchyImage φ] (cauchyExtension φ (t : Plane))) (𝓝 (shapeBoundaryData a φ V t)) := by
  have htcl : (t : Plane) ∈ closure upperHalfPlane := ofReal_mem_closure_upperHalfPlane t
  have hF := ((cauchy_extensions_diffContOnCl_of_holder hφ hα0 hα1 hodd hzero).1.continuousOn
    (t : Plane) htcl).mono subset_closure
  have hFp : Tendsto (cauchy φ) (𝓝[upperHalfPlane] (t : Plane))
      (𝓝 (cauchyExtension φ (t : Plane))) := by
    apply hF.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact cauchyExtension_eq (hφ.continuous hα0).continuousOn hz
  have hG := ((physicalGradientExtension_continuousOn (a := a) (b := b)
    hφ hα0 hα1 hodd hzero) (t : Plane) htcl).mono subset_closure
  have hGp : Tendsto (fun z => gradient (physicalCandidate φ) (cauchy φ z))
      (𝓝[upperHalfPlane] (t : Plane)) (𝓝 (physicalGradientExtension a b φ (t : Plane))) := by
    apply hG.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact physicalGradientExtension_eq_gradient ha hφ hα0 hα1 hodd hzero hpos hlinear hz
  have h := ((hV.continuousAt.tendsto.comp hFp).inner hGp (𝕜 := ℝ)).neg
  have hval : -inner (𝕜 := ℝ) (V (cauchyExtension φ (t : Plane)))
      (physicalGradientExtension a b φ (t : Plane)) = shapeBoundaryData a φ V t := by
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · rw [physicalGradientExtension_ofReal ha hφ hα0 hzero hlinear ht]
      rfl
    · have habs : 1 ≤ |t| := by
        have hn : ¬ (-1 ≤ t ∧ t ≤ 1) := ht
        by_cases hneg : t < -1
        · rw [abs_of_neg (by linarith)]
          linarith
        · have hpos' : 1 < t := lt_of_not_ge (fun hh => hn ⟨le_of_not_gt hneg, hh⟩)
          exact hpos'.le.trans (le_abs_self t)
      have him : (cauchyExtension φ (t : Plane)).im = 0 := by
        simp [cauchyExtension_ofReal, height_zero_of_one_le_abs φ habs]
      have hVz : V (cauchyExtension φ (t : Plane)) = 0 := by
        apply image_eq_zero_of_nmem_tsupport
        intro hm
        have hlt : 0 < (cauchyExtension φ (t : Plane)).im := hVU hm
        simp [him] at hlt
      simp [shapeBoundaryData, hVz]
  rw [hval] at h
  exact tendsto_physical_boundary_of_cauchy_comp hφ hα0 hα1 hodd hzero hpos t h

/-- The harmonic lift plus convection has zero trace on the entire actual
frontier, with no boundary value imposed on the material derivative. -/
theorem convection_add_harmonicLift_boundary_tendsto
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ) (ha : a ≠ 0)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVU : tsupport V ⊆ upperHalfPlane)
    {p : Plane} (hp : p ∈ frontier (cauchyImage φ)) :
    Tendsto (fun w => inner (𝕜 := ℝ) (V w) (gradient (physicalCandidate φ) w) +
      physicalHarmonicLift φ (shapeBoundaryData a φ V) w)
      (𝓝[cauchyImage φ] p) (𝓝 0) := by
  obtain ⟨hg, hgc, hgs⟩ := hEig.shapeBoundaryData_smooth_compact hφ hα0 hα1 hodd hzero hV hVU
  have hgzero (s : ℝ) (hs : 1 ≤ |s|) : shapeBoundaryData a φ V s = 0 := by
    apply image_eq_zero_of_nmem_tsupport
    intro h
    have hmem := hgs h
    have habs : |s| < 1 := abs_lt.mpr hmem
    exact (not_lt_of_ge hs) habs
  rw [frontier_cauchyImage_eq (hφ.continuous hα0) hodd hzero hpos] at hp
  rcases hp with ⟨t, rfl⟩ | hp
  · have hconv := (negative_convection_boundary_tendsto ha hφ hα0 hα1 hodd hzero hpos
      hlinear hV.continuous hVU t).neg
    have hlift := physicalHarmonicLift_boundary_tendsto hφ hα0 hα1 hodd hzero hpos
      hg.continuous hgzero t
    simpa only [neg_neg, neg_add_cancel] using hconv.add hlift
  · have hp0 : p = 0 := hp
    subst p
    have hV0 : V 0 = 0 := by
      apply image_eq_zero_of_nmem_tsupport
      intro h
      have hlt : 0 < (0 : Plane).im := hVU h
      simpa using hlt
    have hconv := ((hV.continuous.tendsto 0).mono_left nhdsWithin_le_nhds).inner
      (gradient_physicalCandidate_tendsto_at_marked ha hφ hα0 hα1 hodd hzero hpos hlinear) (𝕜 := ℝ)
    have hlift := physicalHarmonicLift_marked_boundary_tendsto hφ hα0 hα1 hodd hzero hpos
      hg.continuous.continuousOn
    simpa only [hV0, inner_zero_left, zero_add] using hconv.add hlift

end Torsion.Spectral

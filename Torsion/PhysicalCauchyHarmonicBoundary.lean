import Torsion.PhysicalCauchyHarmonicMarked
import Torsion.CauchyConformalGeometry.CompactifiedClosure

/-!
# The actual compact-data lift at the marked physical boundary

Compactness of finite closed-half-plane parameter sets and nonvanishing of
the actual Cauchy boundary map force inverse coordinates to escape to
infinity near the marked point. Actual Cauchy decay then proves the missing
zero boundary trace along every physical interior approach.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace Torsion.Spectral

/-- Approaching the marked physical point forces actual inverse parameters
to escape every finite ball. No boundary inverse at zero is assigned. -/
theorem cauchyInverse_norm_tendsto_at_marked {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    Tendsto (fun w => ‖cauchyInverse φ w‖) (𝓝[cauchyImage φ] 0) atTop := by
  classical
  apply Filter.tendsto_atTop.mpr
  intro R
  let K : Set Plane := closure upperHalfPlane ∩ closedBall 0 R
  have hK : IsCompact K := (isCompact_closedBall (0 : Plane) R).inter_left isClosed_closure
  have hExt := (cauchy_extensions_diffContOnCl_of_holder hφ hα0 hα1 hodd hzero).1.continuousOn
  have hImage : IsCompact (cauchyExtension φ '' K) := hK.image_of_continuousOn (hExt.mono inter_subset_left)
  have hzeroImage : (0 : Plane) ∉ cauchyExtension φ '' K := by
    rintro ⟨z, hz, heq⟩
    apply cauchyExtension_ne_zero_closedHalfPlane hφ hα0 hα1 hodd hzero hpos
      (show 0 ≤ z.im from by
        simpa only [upperHalfPlane, Complex.closure_setOf_lt_im, mem_setOf_eq] using hz.1) heq
  have hneigh : (cauchyExtension φ '' K)ᶜ ∈ 𝓝 (0 : Plane) :=
    hImage.isClosed.isOpen_compl.mem_nhds hzeroImage
  have hnot : ∀ᶠ w : Plane in 𝓝[cauchyImage φ] 0, w ∉ cauchyExtension φ '' K :=
    nhdsWithin_le_nhds hneigh
  filter_upwards [hnot, self_mem_nhdsWithin] with w hw hwi
  by_contra! hsmall
  apply hw
  refine ⟨cauchyInverse φ w, ⟨subset_closure (cauchyInverse_mem hwi), ?_⟩, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right] using hsmall.le
  · rw [cauchyExtension_eq (hφ.continuous hα0).continuousOn (cauchyInverse_mem hwi)]
    exact cauchy_cauchyInverse hwi

/-- The actual compact-data harmonic lift has zero marked boundary value
along arbitrary physical interior approaches, rather than only a normal
curve. -/
theorem physicalHarmonicLift_marked_boundary_tendsto {φ g : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) :
    Tendsto (physicalHarmonicLift φ g) (𝓝[cauchyImage φ] 0) (𝓝 0) := by
  have h := (cauchy_integral_tendsto_zero
    (Complex.continuous_ofReal.comp_continuousOn hg)
    (cauchyInverse_norm_tendsto_at_marked hφ hα0 hα1 hodd hzero hpos)).const_mul
    (-((Real.pi : Plane)⁻¹))
  have hC : Tendsto (fun w => realCauchy g (cauchyInverse φ w))
      (𝓝[cauchyImage φ] 0) (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply, realCauchy] using h
  simpa only [physicalHarmonicLift, Complex.zero_im] using (Complex.continuous_im.tendsto (0 : Plane)).comp hC

end Torsion.Spectral

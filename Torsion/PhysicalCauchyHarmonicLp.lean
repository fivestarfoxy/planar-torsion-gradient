module

public import Torsion.PhysicalCauchyHarmonicBound

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Finite actual value and gradient Lᵖ norms of the harmonic boundary lift

The bounds are proved for the actual classical function and its actual
gradient on the original Cauchy image. They do not assert that a nonzero
Dirichlet boundary lift has zero-boundary Sobolev membership.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff ENNReal

namespace Torsion.Spectral

theorem physicalHarmonicLift_analyticOnNhd {φ g : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) (hg : Continuous g) :
    AnalyticOnNhd ℂ (realCauchy g ∘ cauchyInverse φ) (cauchyImage φ) :=
  ((realCauchy_differentiableOn hg).comp
    (cauchyInverse_differentiableOn hφ hodd hzero hpos)
    (fun _ hw => cauchyInverse_mem hw)).analyticOnNhd (cauchyImage_isOpen hφ hodd hzero hpos)

theorem physicalHarmonicLift_continuousOn {φ g : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) (hg : Continuous g) :
    ContinuousOn (physicalHarmonicLift φ g) (cauchyImage φ) :=
  Complex.continuous_im.comp_continuousOn
    (physicalHarmonicLift_analyticOnNhd hφ hodd hzero hpos hg).continuousOn

theorem physicalHarmonicLift_gradient_continuousOn {φ g : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) (hg : Continuous g) :
    ContinuousOn (gradient (physicalHarmonicLift φ g)) (cauchyImage φ) := by
  have hB := physicalHarmonicLift_analyticOnNhd hφ hodd hzero hpos hg
  have hG : ContinuousOn (fun w => Complex.I * star (deriv
      (realCauchy g ∘ cauchyInverse φ) w)) (cauchyImage φ) :=
    continuousOn_const.mul (continuous_star.comp_continuousOn hB.deriv.continuousOn)
  apply hG.congr
  intro w hw
  exact (PhysicalTorsion.hasGradientAt_im_of_hasDerivAt (hB w hw).differentiableAt.hasDerivAt).gradient

theorem physicalHarmonicLift_exists_norm_bound {φ g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ Ioo (-1 : ℝ) 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ cauchyImage φ, ‖physicalHarmonicLift φ g w‖ ≤ B := by
  obtain ⟨K, hK⟩ := Shape.exists_lipschitz_scalar_of_contDiff_compact hg hgc
  obtain ⟨B, hB0, hB⟩ := realCauchy_exists_norm_bound hK.holderWith (by norm_num)
    (smooth_compact_interval_zero hgs).1
  refine ⟨B, hB0, ?_⟩
  intro w hw
  exact (Complex.abs_im_le_norm _).trans (hB _ (cauchyInverse_mem hw))

theorem physicalHarmonicLift_memLp {φ g : ℝ → ℝ} {p : ℝ≥0∞}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioo (-1 : ℝ) 1) :
    MemLp (physicalHarmonicLift φ g) p (volume.restrict (cauchyImage φ)) := by
  have hU := cauchyImage_isOpen hφ hodd hzero hpos
  have hb := cauchy_image_isBounded hφ hodd hzero
  haveI : IsFiniteMeasure (volume.restrict (cauchyImage φ)) :=
    ⟨by simpa only [Measure.restrict_apply_univ, cauchyImage] using hb.measure_lt_top⟩
  obtain ⟨B, _, hB⟩ := physicalHarmonicLift_exists_norm_bound (φ := φ) hg hgc hgs
  apply MemLp.of_bound
    ((physicalHarmonicLift_continuousOn hφ hodd hzero hpos hg.continuous).aestronglyMeasurable
      hU.measurableSet) B
  filter_upwards [ae_restrict_mem hU.measurableSet] with w hw
  exact hB w hw

/-- In particular the actual physical harmonic-lift gradient is L² on the
actual Cauchy image; no finite-energy premise is added. -/
theorem physicalHarmonicLift_gradient_memLp
    {a b : ℝ} {φ g : ℝ → ℝ} {C α : ℝ≥0} {p : ℝ≥0∞}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1, realCauchyBoundaryRe φ x = a * height φ x - b)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioo (-1 : ℝ) 1) :
    MemLp (gradient (physicalHarmonicLift φ g)) p (volume.restrict (cauchyImage φ)) := by
  have hc := hφ.continuous hα0
  have hU := cauchyImage_isOpen hc hodd hzero hpos
  have hb := cauchy_image_isBounded hc hodd hzero
  haveI : IsFiniteMeasure (volume.restrict (cauchyImage φ)) :=
    ⟨by simpa only [Measure.restrict_apply_univ, cauchyImage] using hb.measure_lt_top⟩
  obtain ⟨B, _, hB⟩ := physicalHarmonicLift_gradient_exists_norm_bound ha hφ hα0 hα1
    hodd hzero hpos hlinear hg hgc hgs
  apply MemLp.of_bound
    ((physicalHarmonicLift_gradient_continuousOn hc hodd hzero hpos hg.continuous).aestronglyMeasurable
      hU.measurableSet) B
  filter_upwards [ae_restrict_mem hU.measurableSet] with w hw
  exact hB w hw

end Torsion.Spectral

import Torsion.SobolevBoundaryAdmission
import Torsion.PhysicalCauchyZeroExtension
import Torsion.PhysicalCauchyPositivity
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual H¹₀ admissibility of the physical Cauchy candidate

The value is the genuine continuous zero extension. Its weak gradient is
the classical interior gradient extended by zero. Actual global bounds and
the smooth positive-level truncations prove the defining graph closure.
-/
noncomputable section
open Set Filter MeasureTheory Bornology
open scoped Topology ENNReal NNReal ContDiff

namespace Torsion.Spectral

/-- The classical interior gradient, extended by zero to the whole plane. -/
def physicalZeroGradient (φ : ℝ → ℝ) : Plane → Plane :=
  (cauchyImage φ).indicator (gradient (physicalCandidate φ))

theorem physicalZeroGradient_eq {φ : ℝ → ℝ} {w : Plane} (hw : w ∈ cauchyImage φ) :
    physicalZeroGradient φ w = gradient (physicalCandidate φ) w :=
  indicator_of_mem hw _

theorem physicalZeroGradient_eq_zero {φ : ℝ → ℝ} {w : Plane} (hw : w ∉ cauchyImage φ) :
    physicalZeroGradient φ w = 0 := indicator_of_not_mem hw _

theorem physicalCandidate_contDiffOn {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    ContDiffOn ℝ ∞ (physicalCandidate φ) (cauchyImage φ) := by
  intro w hw
  have hB : ContDiffAt ℝ ∞ (physicalHolomorphic φ) w :=
    ((physicalHolomorphic_analyticOnNhd hφ hodd hzero hpos) w hw).contDiffAt.restrict_scalars ℝ
  have him : ContDiffAt ℝ ∞ (fun z : Plane => z.im) w :=
    Complex.imCLM.contDiff.contDiffAt
  have hq : ContDiffAt ℝ ∞ (fun z : Plane => -(z.im) ^ 2 / 2) w := by
    exact (him.pow 2).neg.div_const 2
  exact (hq.add (Complex.imCLM.contDiff.contDiffAt.comp w hB)).contDiffWithinAt

theorem physicalZeroExtension_contDiffOn {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    ContDiffOn ℝ ∞ (physicalZeroExtension φ) (cauchyImage φ) :=
  (physicalCandidate_contDiffOn hφ hodd hzero hpos).congr
    (fun _ hw => physicalZeroExtension_eq hw)

theorem physicalZeroGradient_eq_gradient_on_image {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ cauchyImage φ) :
    physicalZeroGradient φ w = gradient (physicalZeroExtension φ) w := by
  rw [physicalZeroGradient_eq hw]
  have heq : physicalZeroExtension φ =ᶠ[𝓝 w] physicalCandidate φ := by
    filter_upwards [(cauchyImage_isOpen hφ hodd hzero hpos).mem_nhds hw] with z hz
    exact physicalZeroExtension_eq hz
  exact heq.gradient_eq.symm

theorem physicalZeroExtension_laplacian_eq_neg_one {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ cauchyImage φ) :
    WeakHarmonicRegularity.planarLaplacian (physicalZeroExtension φ) w = -1 := by
  have heq : physicalZeroExtension φ =ᶠ[𝓝 w] physicalCandidate φ := by
    filter_upwards [(cauchyImage_isOpen hφ hodd hzero hpos).mem_nhds hw] with z hz
    exact physicalZeroExtension_eq hz
  have hg : gradient (physicalZeroExtension φ) =ᶠ[𝓝 w] gradient (physicalCandidate φ) :=
    heq.gradient
  unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
  rw [hg.fderiv_eq]
  exact physicalCandidate_laplacian_eq_neg_one hφ hodd hzero hpos hw

theorem physicalCandidate_gradient_continuousOn {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    ContinuousOn (gradient (physicalCandidate φ)) (cauchyImage φ) := by
  have hB := physicalHolomorphic_analyticOnNhd hφ hodd hzero hpos
  have hD : ContinuousOn (deriv (physicalHolomorphic φ)) (cauchyImage φ) :=
    hB.deriv.continuousOn
  have hG : ContinuousOn (PhysicalTorsion.candidateGradient (physicalHolomorphic φ))
      (cauchyImage φ) :=
    (continuousOn_const.mul (continuous_star.comp_continuousOn hD)).sub
      ((Complex.continuous_ofReal.comp_continuousOn
        Complex.continuous_im.continuousOn).mul continuousOn_const)
  apply hG.congr
  intro w hw
  exact PhysicalTorsion.gradient_candidate (hB w hw).differentiableAt

/-- The actual physical gradient has a finite uniform bound throughout the
constructed image. No boundary gradient bound is an input. -/
theorem physicalCandidate_gradient_exists_norm_bound
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ cauchyImage φ, ‖gradient (physicalCandidate φ) w‖ ≤ B := by
  have hcont := hφ.continuous hα0
  obtain ⟨BF, hBF0, hBF⟩ := cauchy_exists_norm_bound hcont hodd hzero
  obtain ⟨_, hD, _, _⟩ := cauchy_extensions_diffContOnCl_of_holder
    hφ hα0 hα1 hodd hzero
  obtain ⟨BD, hBD0, hBD⟩ := cauchy_derivative_extension_bounded hcont.continuousOn
    hD.continuousOn (fun z hz => cauchyDerivativeExtension_eq hcont hodd hzero hz)
  refine ⟨|b / a| + BD / |2 * a| + BF, by positivity, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hDraw : ‖deriv (cauchy φ) z‖ ≤ BD := by
    simpa only [cauchyDerivativeExtension_eq hcont hodd hzero hz] using hBD z hz
  have hP : ‖ComplexIdentity.physicalDerivative a b (deriv (cauchy φ) z)‖ ≤
      |b / a| + BD / |2 * a| := by
    unfold ComplexIdentity.physicalDerivative
    apply (norm_sub_le _ _).trans
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_div]
    exact add_le_add_left (div_le_div_of_nonneg_right hDraw (abs_nonneg _)) _
  rw [gradient_physicalCandidate_cauchy ha hφ hα0 hα1 hodd hzero hpos hlinear hz]
  calc
    _ ≤ ‖Complex.I * star (ComplexIdentity.physicalDerivative a b
        (deriv (cauchy φ) z))‖ + ‖((cauchy φ z).im : ℂ) * Complex.I‖ := norm_sub_le _ _
    _ = ‖ComplexIdentity.physicalDerivative a b (deriv (cauchy φ) z)‖ +
        |(cauchy φ z).im| := by simp only [norm_mul, Complex.norm_I, norm_star,
          one_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |b / a| + BD / |2 * a| + BF :=
      add_le_add hP ((Complex.abs_im_le_norm _).trans (hBF z hz))

theorem physicalZeroExtension_hasCompactSupport {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    HasCompactSupport (physicalZeroExtension φ) := by
  have hs : Function.support (physicalZeroExtension φ) ⊆ cauchyImage φ := by
    intro w hw
    by_contra hn
    exact hw (physicalZeroExtension_eq_zero hn)
  exact Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
    ((cauchy_image_isBounded hφ hodd hzero).closure.subset (closure_mono hs))

theorem physicalZeroExtension_memLp {φ : ℝ → ℝ} {p : ℝ≥0∞}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    MemLp (physicalZeroExtension φ) p volume :=
  (physicalZeroExtension_continuous hφ hodd hzero hpos).memLp_of_hasCompactSupport
    (physicalZeroExtension_hasCompactSupport hφ hodd hzero)

theorem physicalZeroGradient_memLp {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0} {p : ℝ≥0∞}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    MemLp (physicalZeroGradient φ) p volume := by
  have hcont := hφ.continuous hα0
  have hD := cauchyImage_isOpen hcont hodd hzero hpos
  have hb := cauchy_image_isBounded hcont hodd hzero
  haveI : IsFiniteMeasure (volume.restrict (cauchyImage φ)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hb.measure_lt_top⟩
  rw [physicalZeroGradient, memLp_indicator_iff_restrict hD.measurableSet]
  obtain ⟨B, _, hB⟩ := physicalCandidate_gradient_exists_norm_bound
    ha hφ hα0 hα1 hodd hzero hpos hlinear
  apply MemLp.of_bound
    ((physicalCandidate_gradient_continuousOn hcont hodd hzero hpos).aestronglyMeasurable
      hD.measurableSet) B
  filter_upwards [ae_restrict_mem hD.measurableSet] with w hw
  exact hB w hw

/-- The candidate and zero-extended classical gradient belong to the actual
H¹₀ graph closure on the actual Cauchy image. No H¹₀ or weak-solution
membership is an assumption of this theorem. -/
theorem physicalCandidate_memH10 {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    MemH10 (cauchyImage φ) (physicalZeroExtension φ) (physicalZeroGradient φ) := by
  have hcont := hφ.continuous hα0
  have hD := cauchyImage_isOpen hcont hodd hzero hpos
  apply BoundaryAdmission.memH10_of_positive_zero_extension hD
    (cauchy_image_isBounded hcont hodd hzero)
    (physicalZeroExtension_continuous hcont hodd hzero hpos)
    (physicalZeroExtension_contDiffOn hcont hodd hzero hpos)
  · intro w hw
    rw [physicalZeroExtension_eq hw]
    exact physicalCandidate_pos_on_cauchyImage hcont hodd hzero hpos hw
  · intro w hw
    exact physicalZeroExtension_eq_zero hw
  · intro w hw
    exact physicalZeroGradient_eq_gradient_on_image hcont hodd hzero hpos hw
  · intro w hw
    exact physicalZeroGradient_eq_zero hw
  · exact physicalZeroExtension_memLp hcont hodd hzero hpos
  · exact physicalZeroGradient_memLp ha hφ hα0 hα1 hodd hzero hpos hlinear

end Torsion.Spectral

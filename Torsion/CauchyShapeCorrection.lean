module

public import Torsion.CauchyShapeBoundaryTrace
public import Torsion.ZeroBoundaryContinuity
public import Torsion.SignedBoundaryAdmission
public import Torsion.PhysicalCauchySobolev
public import Torsion.CauchyConvectionLp
public import Torsion.ShapeEulerianCommutator

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The concrete zero-boundary material correction -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral

/-- Convection plus the actual harmonic extension of its negative trace. -/
def shapeCorrection (a : ℝ) (φ : ℝ → ℝ) (V : Plane → Plane) (w : Plane) : ℝ :=
  inner (𝕜 := ℝ) (V w) (gradient (physicalCandidate φ) w) +
    physicalHarmonicLift φ (shapeBoundaryData a φ V) w

def shapeCorrectionZeroExtension (a : ℝ) (φ : ℝ → ℝ) (V : Plane → Plane) : Plane → ℝ :=
  (cauchyImage φ).indicator (shapeCorrection a φ V)

def shapeCorrectionZeroGradient (a : ℝ) (φ : ℝ → ℝ) (V : Plane → Plane) : Plane → Plane :=
  (cauchyImage φ).indicator (gradient (shapeCorrection a φ V))

theorem shapeCorrection_contDiffOn
    {a : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVU : tsupport V ⊆ upperHalfPlane) :
    ContDiffOn ℝ ∞ (shapeCorrection a φ V) (cauchyImage φ) := by
  have hc := hφ.continuous hα0
  have hU := cauchyImage_isOpen hc hodd hzero hpos
  have hG := contDiffOn_gradient_of_isOpen (physicalCandidate_contDiffOn hc hodd hzero hpos) hU
  have hg := (hEig.shapeBoundaryData_smooth_compact hφ hα0 hα1 hodd hzero hV hVU).1
  have hB := physicalHarmonicLift_analyticOnNhd hc hodd hzero hpos hg.continuous
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  have hlift : ContDiffAt ℝ ∞ (physicalHarmonicLift φ (shapeBoundaryData a φ V)) w :=
    Complex.imCLM.contDiff.contDiffAt.comp w ((hB w hw).contDiffAt.restrict_scalars ℝ)
  exact (hV.contDiffAt.inner ℝ ((hG w hw).contDiffAt (hU.mem_nhds hw))).add hlift

theorem shapeCorrectionZeroExtension_continuous
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ) (ha : a ≠ 0)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVU : tsupport V ⊆ upperHalfPlane) :
    Continuous (shapeCorrectionZeroExtension a φ V) := by
  apply continuous_indicator_of_zero_boundary_tendsto
    (cauchyImage_isOpen (hφ.continuous hα0) hodd hzero hpos)
    (shapeCorrection_contDiffOn hEig hφ hα0 hα1 hodd hzero hpos hV hVU).continuousOn
  intro p hp
  exact convection_add_harmonicLift_boundary_tendsto hEig ha hφ hα0 hα1
    hodd hzero hpos hlinear hV hVU hp

theorem shapeCorrection_gradient
    {a : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVU : tsupport V ⊆ upperHalfPlane)
    {w : Plane} (hw : w ∈ cauchyImage φ) :
    gradient (shapeCorrection a φ V) w =
      gradient (fun z => inner (𝕜 := ℝ) (V z) (gradient (physicalCandidate φ) z)) w +
        gradient (physicalHarmonicLift φ (shapeBoundaryData a φ V)) w := by
  have hc := hφ.continuous hα0
  have hD := cauchyImage_isOpen hc hodd hzero hpos
  have hG := contDiffOn_gradient_of_isOpen (physicalCandidate_contDiffOn hc hodd hzero hpos) hD
  have hconv := hV.contDiffAt.inner ℝ ((hG w hw).contDiffAt (hD.mem_nhds hw))
  have hg := (hEig.shapeBoundaryData_smooth_compact hφ hα0 hα1 hodd hzero hV hVU).1
  have hB := physicalHarmonicLift_analyticOnNhd hc hodd hzero hpos hg.continuous
  have hlift : ContDiffAt ℝ ∞ (physicalHarmonicLift φ (shapeBoundaryData a φ V)) w :=
    Complex.imCLM.contDiff.contDiffAt.comp w ((hB w hw).contDiffAt.restrict_scalars ℝ)
  have h : HasGradientAt (shapeCorrection a φ V)
      (gradient (fun z => inner (𝕜 := ℝ) (V z) (gradient (physicalCandidate φ) z)) w +
        gradient (physicalHarmonicLift φ (shapeBoundaryData a φ V)) w) w := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_add, shapeCorrection, Pi.add_def] using!
      ((hconv.differentiableAt (by simp)).hasGradientAt.hasFDerivAt.add
        (hlift.differentiableAt (by simp)).hasGradientAt.hasFDerivAt)
  exact h.gradient

/-- The constructed material correction belongs to the original H¹₀ graph.
All boundary, smoothness and actual energy requirements are proved here. -/
theorem shapeCorrection_memH10
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVU : tsupport V ⊆ upperHalfPlane) :
    MemH10 (cauchyImage φ) (shapeCorrectionZeroExtension a φ V)
      (shapeCorrectionZeroGradient a φ V) := by
  have hc := hφ.continuous hα0
  have hD := cauchyImage_isOpen hc hodd hzero hpos
  have hs := shapeCorrection_contDiffOn hEig hφ hα0 hα1 hodd hzero hpos hV hVU
  have heq {w : Plane} (hw : w ∈ cauchyImage φ) :
      shapeCorrectionZeroExtension a φ V =ᶠ[𝓝 w] shapeCorrection a φ V := by
    filter_upwards [hD.mem_nhds hw] with z hz
    exact indicator_of_mem hz _
  obtain ⟨hg, hgc, hgs⟩ := hEig.shapeBoundaryData_smooth_compact hφ hα0 hα1 hodd hzero hV hVU
  apply BoundaryAdmission.memH10_of_smooth_zero_extension hD (cauchy_image_isBounded hc hodd hzero)
    (shapeCorrectionZeroExtension_continuous hEig ha.ne' hφ hα0 hα1 hodd hzero hpos hlinear hV hVU)
  · intro w hw
    exact (((hs w hw).contDiffAt (hD.mem_nhds hw)).congr_of_eventuallyEq (heq hw)).contDiffWithinAt
  · intro w hw
    exact indicator_of_notMem hw _
  · intro w hw
    rw [shapeCorrectionZeroGradient, indicator_of_mem hw]
    exact (heq hw).gradient_eq.symm
  · intro w hw
    exact indicator_of_notMem hw _
  · apply (memLp_indicator_iff_restrict hD.measurableSet).mpr
    exact (hEig.cauchyConvection_memLp ha hφ hα0 hα1 hodd hzero hpos hlinear hV hVc hVU).add
      (physicalHarmonicLift_memLp hc hodd hzero hpos hg hgc hgs)
  · apply (memLp_indicator_iff_restrict hD.measurableSet).mpr
    apply ((hEig.cauchyConvection_gradient_memLp ha hφ hα0 hα1 hodd hzero hpos hlinear hV hVc hVU).add
      (physicalHarmonicLift_gradient_memLp ha hφ hα0 hα1 hodd hzero hpos hlinear hg hgc hgs)).ae_eq
    filter_upwards [ae_restrict_mem hD.measurableSet] with w hw
    exact (shapeCorrection_gradient hEig hφ hα0 hα1 hodd hzero hpos hV hVU hw).symm

/-- The actual correction satisfies the differentiated compact-test weak
equation. Its harmonic term contributes zero and its convective term gives
the proved local commutator. -/
theorem shapeCorrection_compact_test_equation
    {a : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVU : tsupport V ⊆ upperHalfPlane)
    {ψ : Plane → ℝ} (hψ : IsTest (cauchyImage φ) ψ) :
    (∫ x, inner (𝕜 := ℝ) (shapeCorrectionZeroGradient a φ V x) (gradient ψ x)) =
      (∫ x, Shape.divergence V x * ψ x) -
        ∫ x, inner (𝕜 := ℝ)
          (Shape.energyVariationOperator V x (gradient (physicalCandidate φ) x)) (gradient ψ x) := by
  have hc := hφ.continuous hα0
  have hD := cauchyImage_isOpen hc hodd hzero hpos
  have hG := contDiffOn_gradient_of_isOpen (physicalCandidate_contDiffOn hc hodd hzero hpos) hD
  have hconv := hV.contDiffOn.inner ℝ hG
  have hg := (hEig.shapeBoundaryData_smooth_compact hφ hα0 hα1 hodd hzero hV hVU).1
  have hB := physicalHarmonicLift_analyticOnNhd hc hodd hzero hpos hg.continuous
  have hlift : ContDiffOn ℝ ∞ (physicalHarmonicLift φ (shapeBoundaryData a φ V)) (cauchyImage φ) := by
    intro w hw
    exact (Complex.imCLM.contDiff.contDiffAt.comp w
      ((hB w hw).contDiffAt.restrict_scalars ℝ)).contDiffWithinAt
  have heq : (fun x => inner (𝕜 := ℝ) (shapeCorrectionZeroGradient a φ V x) (gradient ψ x)) =
      (fun x => inner (𝕜 := ℝ)
        (gradient (fun z => inner (𝕜 := ℝ) (V z) (gradient (physicalCandidate φ) z)) x)
          (gradient ψ x) + inner (𝕜 := ℝ)
            (gradient (physicalHarmonicLift φ (shapeBoundaryData a φ V)) x) (gradient ψ x)) := by
    funext x
    by_cases hx : x ∈ cauchyImage φ
    · rw [shapeCorrectionZeroGradient, indicator_of_mem hx,
        shapeCorrection_gradient hEig hφ hα0 hα1 hodd hzero hpos hV hVU hx, inner_add_left]
    · simp [gradient_eq_zero_of_not_mem_tsupport (fun h => hx (hψ.2.2 h))]
  rw [heq, integral_add (classical_smooth_test_pairing_integrable hD hconv hψ)
    (classical_smooth_test_pairing_integrable hD hlift hψ)]
  rw [classical_harmonic_smooth_test_equation hD hlift
    (fun x hx => physicalHarmonicLift_laplacian_eq_zero hc hodd hzero hpos hg.continuous hx) hψ,
    add_zero]
  exact Shape.eulerian_commutator_local_smooth_test hD hV
    (physicalCandidate_contDiffOn hc hodd hzero hpos)
    (fun x hx => physicalCandidate_laplacian_eq_neg_one hc hodd hzero hpos hx) hψ

/-- At the fixed marked point the correction agrees with its actual
harmonic lift; its flux is therefore the proved mass-normalized boundary
action. This uses the physical straight inward normal. -/
theorem shapeCorrection_hasMarkedFlux
    {a : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVU : tsupport V ⊆ upperHalfPlane) :
    HasMarkedFlux (shapeCorrectionZeroExtension a φ V)
      ((∫ s in Icc (-1 : ℝ) 1, shapeBoundaryData a φ V s) / mass φ) := by
  have hg := (hEig.shapeBoundaryData_smooth_compact hφ hα0 hα1 hodd hzero hV hVU).1
  have hflux := physicalHarmonicLift_hasMarkedFlux (hφ.continuous hα0) hodd hzero hpos
    hg.continuous.continuousOn
  have hVzero : V =ᶠ[𝓝 (0 : Plane)] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro h
    have hlt : 0 < (0 : Plane).im := hVU h
    simp at hlt
  have hline : Tendsto (fun t : ℝ => (t : Plane) * Complex.I) (𝓝[>] 0) (𝓝 (0 : Plane)) := by
    simpa using (((Complex.continuous_ofReal.tendsto 0).mul_const Complex.I).mono_left
      nhdsWithin_le_nhds)
  apply hflux.congr'
  filter_upwards [hline.eventually hVzero,
    eventually_imaginaryAxis_mem_cauchyImage (hφ.continuous hα0) hodd hzero hpos] with t ht htD
  simp only [shapeCorrectionZeroExtension, indicator_of_mem htD, shapeCorrection,
    ht, Pi.zero_apply, inner_zero_left, zero_add]

theorem shapeCorrection_weakHarmonic_on_fixed_patch
    {a b r : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVU : tsupport V ⊆ upperHalfPlane)
    (hpatch : upperHalfPlane ∩ Metric.ball (0 : Plane) (4 * r) ⊆ cauchyImage φ)
    (hVball : ∀ z ∈ Metric.ball (0 : Plane) (4 * r), V z = 0) :
    IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 (4 * r))
      (shapeCorrectionZeroExtension a φ V) (shapeCorrectionZeroGradient a φ V) := by
  refine ⟨(shapeCorrection_memH10 hEig ha hφ hα0 hα1 hodd hzero hpos hlinear hV hVc hVU).distributionalGradient, ?_⟩
  intro ψ hψ
  have he := shapeCorrection_compact_test_equation hEig hφ hα0 hα1 hodd hzero hpos
    hV hVU (hψ.mono hpatch)
  have hz (z : Plane) (hz : z ∈ Metric.ball (0 : Plane) (4 * r)) :
      fderiv ℝ V z = 0 := by
    have heq : V =ᶠ[𝓝 z] 0 := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      exact hVball w hw
    rw [heq.fderiv_eq]
    simp
  have hdiv (z : Plane) : Shape.divergence V z * ψ z = 0 := by
    by_cases hzB : z ∈ Metric.ball (0 : Plane) (4 * r)
    · simp [Shape.divergence, hz z hzB]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hzB (hψ.2.2 h).2), mul_zero]
  have henergy (z : Plane) : inner (𝕜 := ℝ)
      (Shape.energyVariationOperator V z (gradient (physicalCandidate φ) z)) (gradient ψ z) = 0 := by
    by_cases hzB : z ∈ Metric.ball (0 : Plane) (4 * r)
    · simp [Shape.energyVariationOperator, Shape.divergence, hz z hzB]
    · rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hzB (hψ.2.2 h).2), inner_zero_right]
  simpa only [hdiv, henergy, integral_zero, sub_zero] using he

end Torsion.Spectral

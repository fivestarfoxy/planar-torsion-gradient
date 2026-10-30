import Torsion.CauchyShapeCorrection
import Torsion.PhysicalCauchyWeakTorsion
import Torsion.ShapeMaterialEulerian
import Torsion.ShapeMarkedFluxDerivative
import Torsion.WeakDirichletGradientUniqueness

/-!
# The actual localized Hadamard derivative of the Cauchy-domain marked flux

The constructed material derivative is identified with the actual
zero-boundary convective/harmonic correction by the genuine compact-test
equation and H¹₀ uniqueness. Fixed-ball reflection then evaluates its marked
action by the proved physical harmonic lift. No shape-differentiability or
flux-variation formula is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral
open HilbertDirichlet

/-- The actual strong material gradient is the gradient of the constructed
zero-boundary correction, globally a.e. in the original H¹₀ graph. -/
theorem materialDerivative_gradient_eq_shapeCorrection
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVU : tsupport V ⊆ upperHalfPlane) :
    (gradientMap (cauchyImage φ) (Shape.materialDerivative (cauchyImage φ)
      (cauchyImage_isOpen (hφ.continuous hα0) hodd hzero hpos).measurableSet
      (cauchy_image_isBounded (hφ.continuous hα0) hodd hzero) hV hVc) : Plane → Plane) =ᵐ[volume]
      shapeCorrectionZeroGradient a φ V := by
  have hc := hφ.continuous hα0
  have hD := cauchyImage_isOpen hc hodd hzero hpos
  have hb := cauchy_image_isBounded hc hodd hzero
  let p := Shape.materialDerivative (cauchyImage φ) hD.measurableSet hb hV hVc
  have hm := memH10_coordinates p
  apply hm.gradient_ae_eq_of_smooth_test_equation
    (shapeCorrection_memH10 hEig ha hφ hα0 hα1 hodd hzero hpos hlinear hV hVc hVU)
  intro ψ hψ
  have hbase := (Shape.materialSolution_zero_isWeakTorsion (cauchyImage φ)
    hD.measurableSet hb hV hVc).gradient_global_ae_eq hD.measurableSet
    (physicalCandidate_isWeakTorsion ha.ne' hφ hα0 hα1 hodd hzero hpos hlinear)
  rw [Shape.materialDerivative_compact_test_equation (cauchyImage φ) hD.measurableSet hb
    hV hVc hψ,
    shapeCorrection_compact_test_equation hEig hφ hα0 hα1 hodd hzero hpos hV hVU hψ]
  congr 1
  apply integral_congr_ae
  filter_upwards [hbase] with z hz
  by_cases hzD : z ∈ cauchyImage φ
  · rw [hz, physicalZeroGradient_eq hzD]
  · rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hzD (hψ.2.2 h))]
    simp

/-- On a genuine fixed zero-displacement patch, the material derivative's
marked action is the exact mass-normalized conformal boundary integral. -/
theorem materialDerivative_markedGradientFlux_eq
    {a b r : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVU : tsupport V ⊆ upperHalfPlane) (hr : 0 < r)
    (hpatch : upperHalfPlane ∩ Metric.ball (0 : Plane) (4 * r) ⊆ cauchyImage φ)
    (hVball : ∀ z ∈ Metric.ball (0 : Plane) (4 * r), V z = 0) :
    markedGradientFlux r (gradientMap (cauchyImage φ)
      (Shape.materialDerivative (cauchyImage φ)
        (cauchyImage_isOpen (hφ.continuous hα0) hodd hzero hpos).measurableSet
        (cauchy_image_isBounded (hφ.continuous hα0) hodd hzero) hV hVc)) =
      (∫ s in Icc (-1 : ℝ) 1, shapeBoundaryData a φ V s) / mass φ := by
  rw [markedGradientFlux_congr_ae
    (materialDerivative_gradient_eq_shapeCorrection hEig ha hφ hα0 hα1
      hodd hzero hpos hlinear hV hVc hVU) r]
  have hm := (shapeCorrection_memH10 hEig ha hφ hα0 hα1 hodd hzero hpos hlinear
    hV hVc hVU).mono (cauchyImage_isMarked hφ hα0 hα1 hodd hzero hpos).2.2.1
  have hw := shapeCorrection_weakHarmonic_on_fixed_patch hEig ha hφ hα0 hα1 hodd hzero hpos
    hlinear hV hVc hVU hpatch hVball
  have hf := shapeCorrection_hasMarkedFlux hEig hφ hα0 hα1 hodd hzero hpos hV hVU
  exact (hf.eq_fixedGradientKernel hm hw hr zero_lt_one
    (shapeCorrectionZeroExtension_continuous hEig ha.ne' hφ hα0 hα1 hodd hzero hpos
      hlinear hV hVU).continuousOn).symm

/-- The actual localized physical Hadamard derivative, in the original
conformal boundary coordinate. Both differentiation and the integral value
are proved for genuine deformed weak torsion domains. -/
theorem torsionFlux_cauchy_deformation_hasDerivAt
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVU : tsupport V ⊆ upperHalfPlane) :
    HasDerivAt (fun t : ℝ => torsionFlux (Shape.deformation V t '' cauchyImage φ))
      ((∫ s in Icc (-1 : ℝ) 1, shapeBoundaryData a φ V s) / mass φ) 0 := by
  have hVzero : V =ᶠ[𝓝 (0 : Plane)] (fun _ => 0) := by
    apply not_mem_tsupport_iff_eventuallyEq.mp
    intro h
    have hi : 0 < (0 : Plane).im := hVU h
    simp at hi
  obtain ⟨r, hr, hpatch, hVpatch, hd⟩ := Shape.exists_torsionFlux_deformation_hasDerivAt
    (cauchyImage_isMarked hφ hα0 hα1 hodd hzero hpos) hV hVc hVU hVzero
  have hvalue := materialDerivative_markedGradientFlux_eq hEig ha hφ hα0 hα1 hodd hzero hpos
    hlinear hV hVc hVU hr hpatch (fun z hz => (hVpatch z hz).self_of_nhds)
  simpa only [hvalue] using hd

end Torsion.Spectral

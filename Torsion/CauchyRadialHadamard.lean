import Torsion.CauchyShapeHadamard
import Torsion.CauchyRadialHadamardDensity
import Torsion.RadialDeformation
import Torsion.CauchyRadialDomain

/-!
# The actual localized radial Hadamard formula

The actual compact smooth physical deformation is constructed from each
compact smooth angular perturbation. The proved physical flux derivative,
exact domain-image realization and actual oriented argument substitution
give the source angular formula, with no shape-variation premise.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral

variable {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
variable (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
variable (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
variable (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
variable (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
variable (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1, realCauchyBoundaryRe φ x = a * height φ x - b)
variable (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
variable (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)

include hEig ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd

local notation "R" => ContinuousProfiles.extend
  (cauchyRadialProfile ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd)

/-- The genuine two-sided localized Hadamard derivative at the actual
spectral Cauchy reference, for every compact smooth angular direction.
Positivity of the full unit perturbation is not required. -/
theorem cauchy_radial_torsionFlux_hasDerivAt (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ Ioo 0 Real.pi) :
    HasDerivAt (fun t : ℝ => torsionFlux (radialDomain (fun θ => R θ + t * f θ)))
      ((1 / (2 * a * mass φ)) * ∫ θ in Ioo 0 Real.pi, R θ * f θ) 0 := by
  have hR : ContinuousOn R (Icc 0 Real.pi) := (R).continuous.continuousOn
  have hRpos : ∀ θ ∈ Icc 0 Real.pi, 0 < R θ := by
    intro θ hθ
    rw [show R θ = (cauchyRadialProfile ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd) ⟨θ, hθ⟩ from
      ContinuousProfiles.extend_coe _ ⟨θ, hθ⟩]
    exact cauchyRadialProfile_pos ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd _
  obtain ⟨V, δ, hV, hVc, hVU, hδ, _, hVrad, hchange⟩ :=
    Shape.exists_local_radial_deformation hR hRpos hf hfc hfU
  have hderiv := torsionFlux_cauchy_deformation_hasDerivAt hEig ha hφ hα0 hα1 hodd hzero hpos
    hlinear hV hVc hVU
  rw [shapeBoundaryData_radial_integral ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd
    hf.continuous hVrad] at hderiv
  have hbase := radialDomain_cauchyRadialProfile_eq ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| < δ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
  have heq : (fun t : ℝ => torsionFlux (radialDomain (fun θ => R θ + t * f θ))) =ᶠ[𝓝 0]
      (fun t : ℝ => torsionFlux (Shape.deformation V t '' cauchyImage φ)) := by
    filter_upwards [hsmall] with t ht
    obtain ⟨_, e, heq, _, _, himage⟩ := hchange t ht
    have hdomain : Shape.deformation V t '' cauchyImage φ =
        radialDomain (fun θ => R θ + t * f θ) := by
      rw [← hbase]
      simpa only [heq] using himage
    rw [hdomain]
  exact hderiv.congr_of_eventuallyEq heq

end Torsion.Spectral

import Torsion.CauchyTransformBoundaryDerivative

/-! # The actual complex boundary tangent

The extension theorem for real Fréchet derivatives supplies the derivative
of the real boundary parametrization from the genuine continuous Cauchy
extensions. No differentiation of principal values is assumed.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The real boundary parametrization of the actual Cauchy extension has
the actual complex tangent `cauchyDerivativeExtension`. -/
theorem cauchy_boundary_hasDerivAt {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => cauchyExtension φ (t : ℂ))
      (cauchyDerivativeExtension φ (x : ℂ)) x := by
  have hc := hφ.continuous hα0
  have hext := cauchy_extensions_diffContOnCl_of_holder hφ hα0 hα1 hodd hzero
  apply hasDerivAt_boundary_of_continuous_derivative hext.1.continuousOn hext.2.1.continuousOn
  intro z hz
  rw [cauchyDerivativeExtension_eq hc hodd hzero hz]
  have heq : cauchyExtension φ =ᶠ[𝓝 z] cauchy φ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
    exact cauchyExtension_eq hc.continuousOn hw
  exact (hasDerivAt_cauchy hc.continuousOn hz).differentiableAt.hasDerivAt.congr_of_eventuallyEq heq

/-- Continuity of the actual derivative extension upgrades the actual
boundary parametrization to C¹ on the whole real line. -/
theorem cauchy_boundary_contDiff_one {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) :
    ContDiff ℝ 1 (fun t : ℝ => cauchyExtension φ (t : ℂ)) := by
  apply contDiff_one_iff_deriv.2
  refine ⟨fun x => (cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero x).differentiableAt, ?_⟩
  have heq : deriv (fun t : ℝ => cauchyExtension φ (t : ℂ)) =
      fun t : ℝ => cauchyDerivativeExtension φ (t : ℂ) :=
    funext fun x => (cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero x).deriv
  rw [heq]
  exact (cauchy_extensions_diffContOnCl_of_holder hφ hα0 hα1 hodd hzero).2.1.continuousOn.comp_continuous
    Complex.continuous_ofReal ofReal_mem_closure_upperHalfPlane

end Torsion.Spectral

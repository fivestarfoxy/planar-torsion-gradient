module

public import Torsion.CauchyTransformBoundaryExtension
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.Convex

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Differentiating the actual real boundary curve

A continuous extension of a holomorphic derivative supplies the actual
derivative of the boundary parameterization.  Applied to the proved Cauchy
extensions this identifies the derivative of the real Hilbert trace, without
assuming differentiation of principal values.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace Torsion.Spectral

theorem ofReal_mem_closure_upperHalfPlane (x : ℝ) : (x : ℂ) ∈ closure upperHalfPlane := by
  apply mem_closure_iff_nhdsWithin_neBot.mpr
  have hpath : Tendsto (fun c : ℝ => (x : ℂ) + (c⁻¹ : ℝ) * Complex.I) atTop (𝓝 (x : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa using (tendsto_const_nhds.add (h.mul_const Complex.I))
  have him : ∀ᶠ c : ℝ in atTop,
      (x : ℂ) + (c⁻¹ : ℝ) * Complex.I ∈ upperHalfPlane := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    simpa [upperHalfPlane] using inv_pos.2 hc
  exact (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hpath him).neBot

/-- Differentiation at the real boundary follows from the real Fréchet
extension theorem on the convex half-plane. -/
theorem hasDerivAt_boundary_of_continuous_derivative {F D : ℂ → ℂ}
    (hF : ContinuousOn F (closure upperHalfPlane))
    (hD : ContinuousOn D (closure upperHalfPlane))
    (hd : ∀ z ∈ upperHalfPlane, HasDerivAt F (D z) z) (x : ℝ) :
    HasDerivAt (fun t : ℝ => F (t : ℂ)) (D (x : ℂ)) x := by
  have hlim : Tendsto (fun z => fderiv ℝ F z) (𝓝[upperHalfPlane] (x : ℂ))
      (𝓝 (D (x : ℂ) • (1 : ℂ →L[ℝ] ℂ))) := by
    have hc := (hD.smul (continuousOn_const (c := (1 : ℂ →L[ℝ] ℂ))))
      (x : ℂ) (ofReal_mem_closure_upperHalfPlane x)
    have hl := hc.mono subset_closure
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hd z hz).complexToReal_fderiv.fderiv.symm
  have hcl := hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun z hz => (hd z hz).complexToReal_fderiv.differentiableAt.differentiableWithinAt)
    (convex_halfSpace_im_gt (0 : ℝ))
    (isOpen_lt continuous_const Complex.continuous_im)
    (fun z hz => (hF z hz).mono subset_closure) hlim
  have hc := hcl.comp x (Complex.ofRealCLM.hasFDerivAt.hasFDerivWithinAt (s := univ))
    (fun t _ => ofReal_mem_closure_upperHalfPlane t)
  simpa [Function.comp_def] using! hc.hasFDerivAt_of_univ.hasDerivAt

private theorem cauchyExtension_hasDerivAt {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasDerivAt (cauchyExtension φ) (cauchyDerivativeExtension φ z) z := by
  have h := (hasDerivAt_cauchy hφ.continuousOn hz)
  rw [← (hasDerivAt_cauchy hφ.continuousOn hz).deriv,
    ← cauchyDerivativeExtension_eq hφ hodd hzero hz] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
  exact cauchyExtension_eq hφ.continuousOn hw

/-- The genuine real boundary trace of F is differentiable and its
derivative is the negative Hilbert trace of φ. -/
theorem hasDerivAt_realCauchyBoundaryRe_height {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) (x : ℝ) :
    HasDerivAt (realCauchyBoundaryRe (height φ)) (-realCauchyBoundaryRe φ x) x := by
  have hext := cauchy_extensions_diffContOnCl_of_holder hφ hα0 hα1 hodd hzero
  have h := hasDerivAt_boundary_of_continuous_derivative hext.1.continuousOn
    hext.2.1.continuousOn
    (fun z hz => cauchyExtension_hasDerivAt (hφ.continuous hα0) hodd hzero hz) x
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  simpa [Function.comp_def, Complex.reCLM_apply, cauchyExtension_ofReal,
    cauchyDerivativeExtension_ofReal] using hr

end Torsion.Spectral

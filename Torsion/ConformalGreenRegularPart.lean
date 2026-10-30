module

public import Torsion.PhysicalCauchyGreen
public import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A smooth harmonic regular part for the conformal logarithmic kernel

Dividing the injective holomorphic coordinate difference by the physical
coordinate difference removes the pole analytically. The divided difference
has no zeros, including at the source. This provides an actual smooth harmonic
remainder rather than only a limiting value at the pole.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Torsion.HalfPlane

/-- The analytically regularized part of the conformal logarithmic kernel. -/
def conformalGreenRegular (B : Plane → Plane) (v w : Plane) : ℝ :=
  (Real.log ‖B w - star (B v)‖ - Real.log ‖dslope B v w‖) / (2 * Real.pi)

theorem dslope_ne_zero_of_injective {U : Set Plane} {B : Plane → Plane}
    (hB : Set.InjOn B U) {v w : Plane} (hv : v ∈ U) (hw : w ∈ U)
    (hd : deriv B v ≠ 0) : dslope B v w ≠ 0 := by
  by_cases h : w = v
  · simpa [h] using hd
  · rw [dslope_of_ne _ h, slope_def_field]
    exact div_ne_zero (sub_ne_zero.mpr (fun hh => h (hB hw hv hh)))
      (sub_ne_zero.mpr h)

/-- Exact physical logarithmic splitting away from the source. -/
theorem green_comp_eq_fundamental_add_regular {B : Plane → Plane} {v w : Plane}
    (hne : w ≠ v) (hBne : B w ≠ B v) :
    green (B w) (B v) = fundamental v w + conformalGreenRegular B v w := by
  have hlog : Real.log ‖dslope B v w‖ =
      Real.log ‖B w - B v‖ - Real.log ‖w-v‖ := by
    rw [dslope_of_ne _ hne, slope_def_field, norm_div]
    exact Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hBne))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
  unfold green fundamental conformalGreenRegular
  rw [hlog]
  ring

theorem conformalGreenRegular_contDiffOn {U : Set Plane} (hU : IsOpen U)
    {B : Plane → Plane} (hB : DifferentiableOn ℂ B U)
    (hinj : Set.InjOn B U) (hH : ∀ w ∈ U, 0 < (B w).im)
    {v : Plane} (hv : v ∈ U) (hd : deriv B v ≠ 0) :
    ContDiffOn ℝ ∞ (conformalGreenRegular B v) U := by
  have hQ : AnalyticOnNhd ℂ (dslope B v) U :=
    ((Complex.differentiableOn_dslope (hU.mem_nhds hv)).mpr hB).analyticOnNhd hU
  have hBA := hB.analyticOnNhd hU
  intro w hw
  have h1 : ContDiffAt ℝ ∞ (fun z => Real.log ‖B z-star (B v)‖) w := by
    have hc : ContDiffAt ℝ ∞ B w := (hBA w hw).contDiffAt.restrict_scalars ℝ
    exact ((hc.sub contDiffAt_const).norm ℂ
      (reflected_ne (hH w hw) (hH v hv))).log
        (norm_ne_zero_iff.mpr (reflected_ne (hH w hw) (hH v hv)))
  have hn : dslope B v w ≠ 0 := dslope_ne_zero_of_injective hinj hv hw hd
  have hQc : ContDiffAt ℝ ∞ (dslope B v) w := (hQ w hw).contDiffAt.restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun z => Real.log ‖dslope B v z‖) w :=
    (hQc.norm ℂ hn).log (norm_ne_zero_iff.mpr hn)
  exact ((h1.sub h2).div_const _).contDiffWithinAt

/-- The regular remainder is harmonic even at the physical pole. -/
theorem conformalGreenRegular_laplacian_eq_zero {U : Set Plane} (hU : IsOpen U)
    {B : Plane → Plane} (hB : DifferentiableOn ℂ B U)
    (hinj : Set.InjOn B U) (hH : ∀ w ∈ U, 0 < (B w).im)
    {v : Plane} (hv : v ∈ U) (hd : deriv B v ≠ 0) {w : Plane} (hw : w ∈ U) :
    WeakHarmonicRegularity.planarLaplacian (conformalGreenRegular B v) w = 0 := by
  have hQ : AnalyticOnNhd ℂ (dslope B v) U :=
    ((Complex.differentiableOn_dslope (hU.mem_nhds hv)).mpr hB).analyticOnNhd hU
  have hBA := hB.analyticOnNhd hU
  have hQne := dslope_ne_zero_of_injective hinj hv hw hd
  have hg : gradient (conformalGreenRegular B v) =ᶠ[𝓝 w]
      (fun z => (2 * Real.pi)⁻¹ •
        (star (deriv B z / (B z-star (B v))) -
          star (deriv (dslope B v) z / dslope B v z))) := by
    filter_upwards [hU.mem_nhds hw] with z hz
    have hg1 := hasGradientAt_log_norm_comp
      (hB.differentiableAt (hU.mem_nhds hz)).hasDerivAt
      (sub_ne_zero.mp (reflected_ne (hH z hz) (hH v hv)))
    have hqn := dslope_ne_zero_of_injective hinj hv hz hd
    have hg2 := hasGradientAt_log_norm_comp
      (hQ.differentiableOn.differentiableAt (hU.mem_nhds hz)).hasDerivAt hqn
    have hg2' : HasGradientAt (fun u => Real.log ‖dslope B v u‖)
        (star (deriv (dslope B v) z / dslope B v z)) z := by simpa using hg2
    have hh : HasGradientAt (conformalGreenRegular B v)
        ((2 * Real.pi)⁻¹ • (star (deriv B z / (B z-star (B v))) -
          star (deriv (dslope B v) z / dslope B v z))) z := by
      apply hasGradientAt_iff_hasFDerivAt.mpr
      have h := ((hasGradientAt_iff_hasFDerivAt.mp hg1).sub
        (hasGradientAt_iff_hasFDerivAt.mp hg2')).mul_const ((2 * Real.pi)⁻¹)
      simpa only [conformalGreenRegular, map_smul, map_sub, div_eq_mul_inv, Pi.sub_apply] using! h
    exact hh.gradient
  -- The actual differential is linear, so the two zero divergences subtract.
  have hd1 := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp w
    (((hBA.deriv.differentiableOn.differentiableAt (hU.mem_nhds hw)).hasDerivAt.div
      ((hB.differentiableAt (hU.mem_nhds hw)).hasDerivAt.sub_const (star (B v)))
      (reflected_ne (hH w hw) (hH v hv))).complexToReal_fderiv)
  have hd2 := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp w
    (((hQ.deriv.differentiableOn.differentiableAt (hU.mem_nhds hw)).hasDerivAt.div
      (hQ.differentiableOn.differentiableAt (hU.mem_nhds hw)).hasDerivAt hQne).complexToReal_fderiv)
  have hh := (hd1.sub hd2).const_smul ((2 * Real.pi)⁻¹ : ℝ)
  change HasFDerivAt (fun z => (2 * Real.pi)⁻¹ •
    (star (deriv B z / (B z-star (B v))) -
      star (deriv (dslope B v) z / dslope B v z))) _ w at hh
  unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
  rw [hg.fderiv_eq, hh.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.mul_re, Complex.mul_im]
  ring

end Torsion.HalfPlane

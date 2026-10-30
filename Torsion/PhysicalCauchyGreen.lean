module

public import Torsion.HalfPlaneGreen
public import Torsion.PhysicalCauchyKernel
public import Torsion.CauchyConformalGeometry.InverseBoundary
public import Torsion.CauchyConformalGeometry.Infinity
public import Torsion.HalfPlanePoisson
public import Torsion.HalfPlaneGreenInfinity

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The concrete conformal logarithmic kernel

This transports the method-of-images function through the actual proved
Cauchy inverse. In particular the pole is normalized in the physical
Euclidean distance, not merely in a parameter coordinate. Distributional
normalization and its use in the Hadamard formula are separate obligations.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace Torsion.HalfPlane

/-- A nonzero complex derivative preserves the coefficient of the logarithmic
pole under conformal transport, and contributes the exact regular-part term. -/
theorem green_comp_regular_part_tendsto {B : Plane → Plane} {v d : Plane}
    (hB : HasDerivAt B d v) (hd : d ≠ 0) (hv : 0 < (B v).im) :
    Tendsto (fun w => green (B w) (B v) + Real.log ‖w - v‖ / (2 * Real.pi))
      (𝓝[≠] v)
      (𝓝 ((Real.log ‖B v - star (B v)‖ - Real.log ‖d‖) / (2 * Real.pi))) := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hB).norm
  have hlog := hs.log (norm_ne_zero_iff.mpr hd)
  have hcont : ContinuousAt (fun w => B w - star (B v)) v :=
    hB.continuousAt.sub continuousAt_const
  have href : Tendsto (fun w => Real.log ‖B w - star (B v)‖)
      (𝓝[≠] v) (𝓝 (Real.log ‖B v - star (B v)‖)) :=
    (hcont.norm.log (norm_ne_zero_iff.mpr (reflected_ne hv hv))).tendsto.mono_left
      nhdsWithin_le_nhds
  have hlim := (href.sub hlog).div_const (2 * Real.pi)
  apply hlim.congr'
  have hsne : ∀ᶠ w in 𝓝[≠] v, slope B v w ≠ 0 :=
    (hasDerivAt_iff_tendsto_slope.mp hB).eventually (eventually_ne_nhds hd)
  filter_upwards [self_mem_nhdsWithin, hsne] with w hw hsw
  have hwv : w ≠ v := by simpa using hw
  have hBw : B w - B v ≠ 0 := by
    intro h
    apply hsw
    simp [slope_def_field, h]
  have hlogs : Real.log ‖slope B v w‖ =
      Real.log ‖B w - B v‖ - Real.log ‖w - v‖ := by
    simp only [slope_def_field, norm_div]
    exact Real.log_div (norm_ne_zero_iff.mpr hBw)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwv))
  rw [hlogs]
  unfold green
  ring

end Torsion.HalfPlane

namespace Torsion.Spectral

/-- Concrete logarithmic kernel on the actual Cauchy image. -/
def physicalGreen (φ : ℝ → ℝ) (w v : Plane) : ℝ :=
  HalfPlane.green (cauchyInverse φ w) (cauchyInverse φ v)

theorem physicalGreen_symmetric (φ : ℝ → ℝ) (w v : Plane) :
    physicalGreen φ w v = physicalGreen φ v w :=
  HalfPlane.green_symmetric _ _

/-- Conformal covariance is an equality over the actual constructed inverse. -/
theorem physicalGreen_cauchy {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {z ξ : Plane} (hz : z ∈ upperHalfPlane) (hξ : ξ ∈ upperHalfPlane) :
    physicalGreen φ (cauchy φ z) (cauchy φ ξ) = HalfPlane.green z ξ := by
  simp only [physicalGreen, cauchyInverse_cauchy hφ hodd hzero hpos hz,
    cauchyInverse_cauchy hφ hodd hzero hpos hξ]

theorem physicalGreen_pos {φ : ℝ → ℝ} {w v : Plane}
    (hw : w ∈ cauchyImage φ) (hv : v ∈ cauchyImage φ) (hne : w ≠ v) :
    0 < physicalGreen φ w v := by
  apply HalfPlane.green_pos (cauchyInverse_mem hw) (cauchyInverse_mem hv)
  intro h
  apply hne
  rw [← cauchy_cauchyInverse hw, ← cauchy_cauchyInverse hv, h]

/-- The transported kernel is classically harmonic on the actual image
away from its physical pole. -/
theorem physicalGreen_laplacian_eq_zero {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w v : Plane} (hw : w ∈ cauchyImage φ) (hv : v ∈ cauchyImage φ)
    (hne : w ≠ v) :
    WeakHarmonicRegularity.planarLaplacian (fun u => physicalGreen φ u v) w = 0 := by
  have hU := cauchyImage_isOpen hφ hodd hzero hpos
  have hB := cauchyInverse_analyticOnNhd hφ hodd hzero hpos
  apply HalfPlane.green_comp_laplacian_eq_zero hU hB.differentiableOn
    hB.deriv.differentiableOn hw
  · exact sub_ne_zero.mp (HalfPlane.reflected_ne (cauchyInverse_mem hw) (cauchyInverse_mem hv))
  · intro h
    apply hne
    rw [← cauchy_cauchyInverse hw, ← cauchy_cauchyInverse hv, h]

/-- The transported kernel has zero boundary trace at every finite Cauchy
parameter, along arbitrary physical interior approaches. -/
theorem physicalGreen_finite_boundary_tendsto {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {v : Plane} (hv : v ∈ cauchyImage φ) (t : ℝ) :
    Tendsto (fun w => physicalGreen φ w v)
      (𝓝[cauchyImage φ] (cauchyExtension φ (t : Plane))) (𝓝 0) := by
  have hvim : 0 < (cauchyInverse φ v).im := cauchyInverse_mem hv
  have hne₁ : (t : Plane) - star (cauchyInverse φ v) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.star_def,
      Complex.conj_im, Complex.zero_im] at hi
    linarith
  have hne₂ : (t : Plane) - cauchyInverse φ v ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at hi
    linarith
  have hcont₁ : ContinuousAt (fun z : Plane => Real.log ‖z-star (cauchyInverse φ v)‖)
      (t : Plane) :=
    (continuousAt_id.sub continuousAt_const).norm.log (norm_ne_zero_iff.mpr hne₁)
  have hcont₂ : ContinuousAt (fun z : Plane => Real.log ‖z-cauchyInverse φ v‖)
      (t : Plane) :=
    (continuousAt_id.sub continuousAt_const).norm.log (norm_ne_zero_iff.mpr hne₂)
  have hcont : ContinuousAt (fun z => HalfPlane.green z (cauchyInverse φ v))
      (t : Plane) := (hcont₁.sub hcont₂).div_const _
  have hlim := hcont.tendsto.comp
    (cauchyInverse_boundary_tendsto hφ hα0 hα1 hodd hzero hpos t)
  simpa only [HalfPlane.green_real_boundary, physicalGreen, Function.comp_apply] using! hlim

/-- The logarithmic singularity has exactly coefficient `-1/(2π)` in
physical distance. The inverse derivative determines only the regular part. -/
theorem physicalGreen_regular_part_tendsto {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    Tendsto (fun w => physicalGreen φ w (cauchy φ z) +
      Real.log ‖w - cauchy φ z‖ / (2 * Real.pi))
      (𝓝[≠] (cauchy φ z))
      (𝓝 ((Real.log ‖z - star z‖ -
        Real.log ‖(deriv (cauchy φ) z)⁻¹‖) / (2 * Real.pi))) := by
  have h := HalfPlane.green_comp_regular_part_tendsto
    (cauchyInverse_hasDerivAt hφ hodd hzero hpos hz)
    (inv_ne_zero (cauchy_derivative_ne_zero hφ hodd hzero hpos hz))
    (show 0 < (cauchyInverse φ (cauchy φ z)).im by
      rw [cauchyInverse_cauchy hφ hodd hzero hpos hz]; exact hz)
  simpa only [physicalGreen, cauchyInverse_cauchy hφ hodd hzero hpos hz] using h

/-- The marked harmonic function has exactly the Poisson transformation
factor `1/|F∞′(0)|` in the actual infinity chart. -/
theorem physicalMarkedKernel_eq_poisson_infinity {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) (w : Plane) :
    physicalMarkedKernel φ w =
      HalfPlane.poisson (-(cauchyInverse φ w)⁻¹) 0 /
        ‖deriv (cauchyAtInfinity φ) 0‖ := by
  have hM := mass_pos hφ hpos
  have hd : ‖deriv (cauchyAtInfinity φ) 0‖ = mass φ / Real.pi := by
    rw [(cauchyAtInfinity_hasDerivAt_zero hφ).deriv]
    simp [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos hM, div_eq_mul_inv, mul_comm]
  rw [hd, HalfPlane.poisson_infinity_coordinate]
  unfold physicalMarkedKernel
  field_simp [Real.pi_ne_zero, hM.ne']

/-- The source Green quotient at the marked physical boundary point is the
previously constructed harmonic marked kernel, with no adjustable factor. -/
theorem physicalGreen_marked_source_quotient_tendsto {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ cauchyImage φ) :
    Tendsto (fun t : ℝ =>
      physicalGreen φ w (cauchyAtInfinity φ ((t : Plane) * Complex.I)) /
        (cauchyAtInfinity φ ((t : Plane) * Complex.I)).im)
      (𝓝[>] 0) (𝓝 (physicalMarkedKernel φ w)) := by
  have hM := mass_pos hφ.continuousOn hpos
  have hpath : HasDerivAt (fun t : ℝ => (t : Plane) * Complex.I) Complex.I 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I
  have hF := (cauchyAtInfinity_hasDerivAt_zero hφ.continuousOn).complexToReal_fderiv
  have hFpath := hF.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hFpath
  have hd : HasDerivAt
      (fun t : ℝ => (cauchyAtInfinity φ ((t : Plane) * Complex.I)).im)
      (mass φ / Real.pi) 0 := by
    convert! him using 1 <;>
      first | rfl | (simp [ContinuousLinearMap.smul_apply, Complex.mul_re, Complex.mul_im,
        div_eq_mul_inv, mul_comm] <;> ring)
  have hden : Tendsto (fun t : ℝ =>
      (cauchyAtInfinity φ ((t : Plane) * Complex.I)).im / t)
      (𝓝[>] 0) (𝓝 (mass φ / Real.pi)) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hd.tendsto_slope_zero_right
  have hnum := (HalfPlane.green_source_infinity_div_t_tendsto
    (cauchyInverse φ w)).mono_left (nhdsGT_le_nhdsNE 0)
  have hlim := hnum.div hden (div_ne_zero hM.ne' Real.pi_ne_zero)
  have hvalue : ((cauchyInverse φ w).im / Real.pi) / (mass φ / Real.pi) =
      physicalMarkedKernel φ w := by
    unfold physicalMarkedKernel
    field_simp [hM.ne', Real.pi_ne_zero]
  rw [hvalue] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have htC : (t : Plane) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne') Complex.I_ne_zero
  have hz : (t⁻¹ : ℝ) * Complex.I ∈ upperHalfPlane := by
    simpa [upperHalfPlane] using inv_pos.mpr htpos
  have hcoord : -((t : Plane) * Complex.I)⁻¹ = (t⁻¹ : ℝ) * Complex.I := by
    simp [mul_inv_rev, Complex.inv_I, mul_comm]
  simp only [Pi.div_apply]
  rw [cauchyAtInfinity_eq htC, hcoord]
  unfold physicalGreen
  rw [cauchyInverse_cauchy hφ hodd hzero hpos hz]
  exact div_div_div_cancel_right₀ htpos.ne' _ _

end Torsion.Spectral

module

public import Torsion.PhysicalTorsionCalculus
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The logarithmic Green kernel of the upper half-plane

The coefficient is fixed by the two-dimensional fundamental solution
`-(2π)⁻¹ log |z-w|`. These results concern concrete scalar functions, not an
assumed Green-function certificate. Distributional normalization is a separate
step from the harmonicity and the exact logarithmic singularity proved here.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace Torsion.HalfPlane

/-- The method-of-images logarithmic kernel, with the `-ΔG=δ` coefficient. -/
def green (z w : Plane) : ℝ :=
  (Real.log ‖z - star w‖ - Real.log ‖z - w‖) / (2 * Real.pi)

/-- The planar fundamental solution, retaining its standard logarithmic sign. -/
def fundamental (w z : Plane) : ℝ := -Real.log ‖z-w‖ / (2 * Real.pi)

theorem green_symmetric (z w : Plane) : green z w = green w z := by
  have h₁ : ‖z - star w‖ = ‖w - star z‖ := by
    calc
      ‖z - star w‖ = ‖star (z - star w)‖ := (norm_star _).symm
      _ = ‖star z - w‖ := by simp
      _ = ‖w - star z‖ := norm_sub_rev _ _
  simp only [green, h₁, norm_sub_rev z w]

theorem green_real_boundary (x : ℝ) (w : Plane) : green (x : Plane) w = 0 := by
  have h : ‖(x : Plane) - star w‖ = ‖(x : Plane) - w‖ := by
    simpa using (norm_star ((x : Plane) - w))
  change (Real.log ‖(x : Plane) - star w‖ - Real.log ‖(x : Plane) - w‖) / _ = 0
  rw [h]
  simp

theorem reflected_ne {z w : Plane} (hz : 0 < z.im) (hw : 0 < w.im) :
    z - star w ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hi
  linarith

theorem norm_reflected_gt {z w : Plane} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖z - w‖ < ‖z - star w‖ := by
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [mul_pos hz hw]

theorem green_pos {z w : Plane} (hz : 0 < z.im) (hw : 0 < w.im) (hne : z ≠ w) :
    0 < green z w := by
  apply div_pos _ (mul_pos (by norm_num) Real.pi_pos)
  exact sub_pos.mpr (Real.strictMonoOn_log (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    (norm_pos_iff.mpr (reflected_ne hz hw)) (norm_reflected_gt hz hw))

/-- Exact cancellation of the pole leaves the reflected, regular logarithm. -/
theorem green_regular_part (z w : Plane) :
    green z w + Real.log ‖z - w‖ / (2 * Real.pi) =
      Real.log ‖z - star w‖ / (2 * Real.pi) := by
  unfold green
  ring

/-- The regular part extends continuously to the pole in the upper half-plane. -/
theorem green_regular_part_tendsto {w : Plane} (hw : 0 < w.im) :
    Tendsto (fun z => green z w + Real.log ‖z - w‖ / (2 * Real.pi))
      (𝓝 w) (𝓝 (Real.log ‖w - star w‖ / (2 * Real.pi))) := by
  simp only [green_regular_part]
  exact (((continuous_id.sub continuous_const).norm.continuousAt.log
    (norm_ne_zero_iff.mpr (reflected_ne hw hw))).div_const _).tendsto

/-- The real logarithmic potential has the reciprocal complex gradient. -/
theorem hasGradientAt_log_norm {z : Plane} (hz : z ≠ 0) :
    HasGradientAt (fun u : Plane => Real.log ‖u‖) (star z⁻¹) z := by
  have h := ((hasFDerivAt_id z).norm_sq.log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))).mul_const (2⁻¹ : ℝ)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! h using 1
  · ext u
    norm_num [Real.log_pow]
    ring
  · ext u
    simp [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
      Complex.inner, Complex.inv_re, Complex.inv_im, Complex.normSq_eq_norm_sq,
      Complex.star_def, Complex.mul_re, Complex.mul_im]
    ring

theorem hasGradientAt_log_norm_sub (w : Plane) {z : Plane} (hz : z ≠ w) :
    HasGradientAt (fun u : Plane => Real.log ‖u-w‖) (star (z-w)⁻¹) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert (hasGradientAt_iff_hasFDerivAt.mp
    (hasGradientAt_log_norm (sub_ne_zero.mpr hz))).comp z
      ((hasFDerivAt_id z).sub_const w) using 1 <;> simp [Function.comp_def]

theorem fundamental_hasGradientAt {z w : Plane} (hz : z ≠ w) :
    HasGradientAt (fundamental w) (-(2 * Real.pi)⁻¹ • star (z-w)⁻¹) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have h := (hasGradientAt_iff_hasFDerivAt.mp (hasGradientAt_log_norm_sub w hz)).neg.mul_const
    ((2 * Real.pi)⁻¹)
  simpa only [fundamental, div_eq_mul_inv, map_smul, map_neg, neg_smul, smul_neg] using! h

/-- Pairing with the radius vector incorporates the circle's arclength
factor. Its integral over one turn is exactly `-1`, fixing the source mass. -/
theorem fundamental_radial_flux {z w : Plane} (hz : z ≠ w) :
    inner (𝕜 := ℝ) (gradient (fundamental w) z) (z-w) = -(2 * Real.pi)⁻¹ := by
  rw [(fundamental_hasGradientAt hz).gradient, real_inner_smul_left]
  have hi : inner (𝕜 := ℝ) (star (z-w)⁻¹) (z-w) = 1 := by
    simp [Complex.inner, Complex.star_def, ← Complex.mul_re,
      mul_inv_cancel₀ (sub_ne_zero.mpr hz)]
  rw [hi, mul_one]

/-- Every positively oriented circle surrounding the pole has total outward
fundamental-solution flux `-1`. The radius vector here is the unit normal
multiplied by arclength per unit angle. -/
theorem fundamental_circle_flux (w : Plane) {r : ℝ} (hr : 0 < r) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      inner (𝕜 := ℝ)
        (gradient (fundamental w) (w + (r : Plane) * Complex.exp ((θ : Plane) * Complex.I)))
        ((r : Plane) * Complex.exp ((θ : Plane) * Complex.I))) = -1 := by
  have hpoint (θ : ℝ) : w + (r : Plane) * Complex.exp ((θ : Plane) * Complex.I) ≠ w := by
    simpa only [add_ne_left] using mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
      (Complex.exp_ne_zero _)
  have hflux (θ : ℝ) :
      inner (𝕜 := ℝ)
        (gradient (fundamental w) (w + (r : Plane) * Complex.exp ((θ : Plane) * Complex.I)))
        ((r : Plane) * Complex.exp ((θ : Plane) * Complex.I)) = -(2 * Real.pi)⁻¹ := by
    simpa using fundamental_radial_flux (hpoint θ)
  simp_rw [hflux]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

theorem green_hasGradientAt {z w : Plane}
    (hr : z ≠ star w) (hp : z ≠ w) :
    HasGradientAt (fun u => green u w)
      ((2 * Real.pi)⁻¹ • (star (z-star w)⁻¹ - star (z-w)⁻¹)) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have h := ((hasGradientAt_iff_hasFDerivAt.mp (hasGradientAt_log_norm_sub (star w) hr)).sub
    (hasGradientAt_iff_hasFDerivAt.mp (hasGradientAt_log_norm_sub w hp))).mul_const ((2*Real.pi)⁻¹)
  simpa only [green, div_eq_mul_inv, map_smul, map_sub] using! h

private theorem divergence_star_of_hasDerivAt {f : Plane → Plane} {d z : Plane}
    (h : HasDerivAt f d z) :
    WeakHarmonicRegularity.planarDivergence (fun u => star (f u)) z = 0 := by
  have hd := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z
    h.complexToReal_fderiv
  change HasFDerivAt (fun u => star (f u)) _ z at hd
  unfold WeakHarmonicRegularity.planarDivergence
  rw [hd.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.mul_re, Complex.mul_im]

/-- Chain rule for a logarithmic potential under an actual holomorphic map. -/
theorem hasGradientAt_log_norm_comp {B : Plane → Plane} {d z c : Plane}
    (hB : HasDerivAt B d z) (hne : B z ≠ c) :
    HasGradientAt (fun u => Real.log ‖B u-c‖) (star (d / (B z-c))) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have h := (hasGradientAt_iff_hasFDerivAt.mp
    (hasGradientAt_log_norm_sub c hne)).comp z hB.complexToReal_fderiv
  convert! h using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
    Complex.inner, Complex.star_def, div_eq_mul_inv, Complex.mul_re, Complex.mul_im]
  ring

/-- Holomorphic pullback preserves classical harmonicity of the logarithmic
potential, with no global branch of the complex logarithm required. -/
theorem log_norm_comp_laplacian_eq_zero {U : Set Plane} (hU : IsOpen U)
    {B : Plane → Plane} (hB : DifferentiableOn ℂ B U)
    (hD : DifferentiableOn ℂ (deriv B) U) {z c : Plane}
    (hz : z ∈ U) (hne : B z ≠ c) :
    WeakHarmonicRegularity.planarLaplacian (fun u => Real.log ‖B u-c‖) z = 0 := by
  have hneN : ∀ᶠ u in 𝓝 z, B u ≠ c :=
    (hB.differentiableAt (hU.mem_nhds hz)).continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds hne)
  have heq : gradient (fun u => Real.log ‖B u-c‖) =ᶠ[𝓝 z]
      (fun u => star (deriv B u / (B u-c))) := by
    filter_upwards [hU.mem_nhds hz, hneN] with u hu huc
    exact (hasGradientAt_log_norm_comp
      (hB.differentiableAt (hU.mem_nhds hu)).hasDerivAt huc).gradient
  unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
  rw [heq.fderiv_eq]
  exact divergence_star_of_hasDerivAt
    ((hD.differentiableAt (hU.mem_nhds hz)).hasDerivAt.div
      ((hB.differentiableAt (hU.mem_nhds hz)).hasDerivAt.sub_const c)
      (sub_ne_zero.mpr hne))

theorem green_comp_hasGradientAt {B : Plane → Plane} {d z w : Plane}
    (hB : HasDerivAt B d z) (hr : B z ≠ star w) (hp : B z ≠ w) :
    HasGradientAt (fun u => green (B u) w)
      ((2 * Real.pi)⁻¹ • (star (d / (B z-star w)) - star (d / (B z-w)))) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have h := ((hasGradientAt_iff_hasFDerivAt.mp (hasGradientAt_log_norm_comp hB hr)).sub
    (hasGradientAt_iff_hasFDerivAt.mp (hasGradientAt_log_norm_comp hB hp))).mul_const ((2*Real.pi)⁻¹)
  simpa only [green, div_eq_mul_inv, map_smul, map_sub] using! h

/-- Classical conformal covariance of the harmonic equation for the concrete
Green formula. This result is independent of distributional source admission. -/
theorem green_comp_laplacian_eq_zero {U : Set Plane} (hU : IsOpen U)
    {B : Plane → Plane} (hB : DifferentiableOn ℂ B U)
    (hD : DifferentiableOn ℂ (deriv B) U) {z w : Plane}
    (hz : z ∈ U) (hr : B z ≠ star w) (hp : B z ≠ w) :
    WeakHarmonicRegularity.planarLaplacian (fun u => green (B u) w) z = 0 := by
  have hBr : ∀ᶠ u in 𝓝 z, B u ≠ star w :=
    (hB.differentiableAt (hU.mem_nhds hz)).continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds hr)
  have hBp : ∀ᶠ u in 𝓝 z, B u ≠ w :=
    (hB.differentiableAt (hU.mem_nhds hz)).continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds hp)
  have heq : gradient (fun u => green (B u) w) =ᶠ[𝓝 z]
      (fun u => (2 * Real.pi)⁻¹ •
        (star (deriv B u / (B u-star w)) - star (deriv B u / (B u-w)))) := by
    filter_upwards [hU.mem_nhds hz, hBr, hBp] with u hu hur hup
    exact (green_comp_hasGradientAt
      (hB.differentiableAt (hU.mem_nhds hu)).hasDerivAt hur hup).gradient
  have hd₁ := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z
    (((hD.differentiableAt (hU.mem_nhds hz)).hasDerivAt.div
      ((hB.differentiableAt (hU.mem_nhds hz)).hasDerivAt.sub_const (star w))
      (sub_ne_zero.mpr hr)).complexToReal_fderiv)
  have hd₂ := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z
    (((hD.differentiableAt (hU.mem_nhds hz)).hasDerivAt.div
      ((hB.differentiableAt (hU.mem_nhds hz)).hasDerivAt.sub_const w)
      (sub_ne_zero.mpr hp)).complexToReal_fderiv)
  have hd := (hd₁.sub hd₂).const_smul ((2 * Real.pi)⁻¹ : ℝ)
  change HasFDerivAt
    (fun u => (2 * Real.pi)⁻¹ •
      (star (deriv B u / (B u-star w)) - star (deriv B u / (B u-w)))) _ z at hd
  unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
  rw [heq.fderiv_eq, hd.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The logarithm of distance is classically harmonic off its pole. -/
theorem log_norm_sub_laplacian_eq_zero {z w : Plane} (hz : z ≠ w) :
    WeakHarmonicRegularity.planarLaplacian (fun u => Real.log ‖u-w‖) z = 0 := by
  have heq : gradient (fun u : Plane => Real.log ‖u-w‖) =ᶠ[𝓝 z]
      (fun u => star (u-w)⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz] with u hu
    exact (hasGradientAt_log_norm_sub w hu).gradient
  unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
  rw [heq.fderiv_eq]
  exact divergence_star_of_hasDerivAt (((hasDerivAt_id z).sub_const w).inv
    (sub_ne_zero.mpr hz))

/-- The image kernel is genuinely harmonic in its first variable away from
the source and its reflected source. -/
theorem green_laplacian_eq_zero {z w : Plane}
    (hr : z ≠ star w) (hp : z ≠ w) :
    WeakHarmonicRegularity.planarLaplacian (fun u => green u w) z = 0 := by
  have heq : gradient (fun u => green u w) =ᶠ[𝓝 z]
      (fun u => (2 * Real.pi)⁻¹ • (star (u-star w)⁻¹ - star (u-w)⁻¹)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hr,
      isOpen_compl_singleton.mem_nhds hp] with u hur hup
    exact (green_hasGradientAt hur hup).gradient
  have hd₁ := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z
    ((((hasDerivAt_id z).sub_const (star w)).inv
      (sub_ne_zero.mpr hr)).complexToReal_fderiv)
  have hd₂ := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z
    ((((hasDerivAt_id z).sub_const w).inv
      (sub_ne_zero.mpr hp)).complexToReal_fderiv)
  have hd := (hd₁.sub hd₂).const_smul ((2 * Real.pi)⁻¹ : ℝ)
  change HasFDerivAt
    (fun u => (2 * Real.pi)⁻¹ • (star (u-star w)⁻¹ - star (u-w)⁻¹)) _ z at hd
  unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
  rw [heq.fderiv_eq, hd.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The inward source derivative at a finite boundary point is the normalized
half-plane Poisson density. This computes the Green-to-Poisson normalization
directly from the logarithmic formula. -/
theorem green_hasDerivAt_boundary_source {z : Plane} (hz : 0 < z.im) (x : ℝ) :
    HasDerivAt (fun t : ℝ => green z ((x : Plane) + (t : Plane) * Complex.I))
      (z.im / (Real.pi * ((z.re-x)^2 + z.im^2))) 0 := by
  have hD : (z.re-x)^2 + z.im^2 ≠ 0 := by nlinarith [sq_nonneg (z.re-x)]
  have h₁ : HasDerivAt (fun t : ℝ => (z.re-x)^2 + (z.im+t)^2)
      (2*z.im) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_add z.im).pow 2).const_add ((z.re-x)^2)
      using 1 <;> simp <;> ring
  have h₂ : HasDerivAt (fun t : ℝ => (z.re-x)^2 + (z.im-t)^2)
      (-2*z.im) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_sub z.im).pow 2).const_add ((z.re-x)^2)
      using 1 <;> simp <;> ring
  have hd := ((h₁.log (by simpa using hD)).sub (h₂.log (by simpa using hD))).div_const
    (4 * Real.pi)
  have hlog (u : Plane) : Real.log ‖u‖ = Real.log (Complex.normSq u) / 2 := by
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    ring
  convert hd using 1
  · ext t
    simp only [Pi.sub_apply, green, hlog, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  · simp only [add_zero, sub_zero]
    field_simp
    ring

end Torsion.HalfPlane

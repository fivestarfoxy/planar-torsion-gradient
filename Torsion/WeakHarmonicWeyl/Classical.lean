module

public import Torsion.WeakHarmonicWeyl
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The holomorphic gradient of a smooth planar harmonic function

The Cauchy--Riemann equations follow from the actual Hessian symmetry and
vanishing Laplacian, not from a separate complex differentiability assumption.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion.WeakHarmonicRegularity

/-- Smoothness of the actual real gradient. -/
theorem gradient_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (gradient f) := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.contDiff.comp
    (hf.fderiv_right (by simp))

/-- The differential of the gradient is the Hessian identified by Riesz. -/
theorem fderiv_gradient_inner {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v w : Plane) :
    inner (𝕜 := ℝ) (fderiv ℝ (gradient f) x v) w =
      fderiv ℝ (fderiv ℝ f) x v w := by
  have hfd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiable (by norm_num)
  have hd := (InnerProductSpace.toDual ℝ Plane).symm.hasFDerivAt.comp x
    (hfd x).hasFDerivAt
  change HasFDerivAt (gradient f) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  exact InnerProductSpace.toDual_symm_apply

/-- The Hessian of a smooth real scalar function is symmetric, expressed in
terms of the actual vector gradient. -/
theorem fderiv_gradient_inner_symm {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v w : Plane) :
    inner (𝕜 := ℝ) (fderiv ℝ (gradient f) x v) w =
      inner (𝕜 := ℝ) (fderiv ℝ (gradient f) x w) v := by
  rw [fderiv_gradient_inner hf, fderiv_gradient_inner hf]
  have hle : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    norm_num [minSmoothness_of_isRCLikeNormedField]
  exact (hf.contDiffAt.isSymmSndFDerivAt hle).eq v w

/-- Conjugating the gradient gives the classical complex derivative field
`f_x - i f_y`. -/
def complexGradient (f : Plane → ℝ) : ℂ → ℂ := fun z => star (gradient f z)

/-- The actual conjugate-gradient field is complex differentiable at every
point where the smooth function's Laplacian vanishes. -/
theorem complexGradient_differentiableAt {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) {x : Plane} (hh : planarLaplacian f x = 0) :
    DifferentiableAt ℂ (complexGradient f) x := by
  let G : Plane →L[ℝ] Plane := fderiv ℝ (gradient f) x
  have hsymm := fderiv_gradient_inner_symm hf x (1 : Plane) Complex.I
  have htrace : (G 1).re + (G Complex.I).im = 0 := hh
  have hcross : (G 1).im = (G Complex.I).re := by
    simpa [Complex.inner, Complex.mul_re, G] using hsymm
  have hdiff : DifferentiableAt ℝ (complexGradient f) x :=
    Complex.conjCLE.differentiableAt.comp x ((gradient_contDiff hf).differentiable (by simp) x)
  rw [differentiableAt_iff_restrictScalars ℝ hdiff]
  refine ⟨ContinuousLinearMap.toSpanSingleton ℂ (star (G 1)), ?_⟩
  have hderiv : fderiv ℝ (complexGradient f) x =
      (Complex.conjCLE : Plane →L[ℝ] Plane).comp G := by
    exact (Complex.conjCLE.hasFDerivAt.comp x
      ((gradient_contDiff hf).differentiable (by simp) x).hasFDerivAt).fderiv
  rw [hderiv]
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = z.re • (1 : Plane) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  change z • star (G 1) = star (G z)
  have hdiag : (G Complex.I).im = -(G 1).re := by linarith
  rw [hz]
  simp only [map_add, map_smul]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im,
      Complex.smul_re, Complex.smul_im, hcross, hdiag]

/-- The angular mean-value identity is derived from the actual Cauchy formula.
It is a proved analytic tool for the holomorphic-gradient route to Weyl. -/
theorem holomorphic_circle_mean_value {F : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ F (Metric.closedBall c r)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, F (circleMap c r θ)) =
      (2 * Real.pi : ℂ) * F c := by
  have hcenter : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have H := hd.circleIntegral_sub_inv_smul hcenter
  unfold circleIntegral at H
  have hkernel (θ : ℝ) : deriv (circleMap c r) θ •
      ((circleMap c r θ - c)⁻¹ • F (circleMap c r θ)) =
      Complex.I * F (circleMap c r θ) := by
    have hne : circleMap c r θ - c ≠ 0 :=
      sub_ne_zero.mpr (circleMap_ne_mem_ball hcenter θ)
    have hc : circleMap 0 r θ = circleMap c r θ - c := by simp [circleMap]
    rw [deriv_circleMap, hc]
    simp only [smul_eq_mul]
    have hne0 : circleMap 0 r θ ≠ 0 := by rwa [hc]
    field_simp [hne0]
  simp_rw [hkernel] at H
  rw [intervalIntegral.integral_const_mul] at H
  have H' : Complex.I * (∫ θ in (0 : ℝ)..2 * Real.pi, F (circleMap c r θ)) =
      Complex.I * ((2 * Real.pi : ℂ) * F c) := by
    calc
      _ = (2 * Real.pi * Complex.I : ℂ) * F c := by
        simpa only [smul_eq_mul] using H
      _ = _ := by ring
  exact mul_left_cancel₀ Complex.I_ne_zero H'

end Torsion.WeakHarmonicRegularity

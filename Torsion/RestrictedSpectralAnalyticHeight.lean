module

public import Torsion.RestrictedSpectralBoundaryRegularity
public import Torsion.ComplexUpperPrimitive
public import Torsion.ComplexSchwarzReflection
public import Torsion.ComplexODEContinuation
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Interior analytic continuation of the actual spectral height

The weak eigenfunction equation first regularizes the real Cauchy boundary
value. A genuine continuous upper half-plane primitive turns that boundary
ODE into a real-valued holomorphic reflection problem. An integrating
factor then continues the primitive, and hence the original Cauchy map.
-/
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal ContDiff ComplexConjugate

namespace Torsion.Spectral
open Torsion.ComplexReflection

/-- The genuine Cauchy transform of the actual height has a holomorphic
continuation through each interior real point, even when the original
weak eigenfunction has no chosen pointwise regularity. -/
theorem IsRestrictedEigenfunction.exists_height_Cauchy_extension_of_odd
    {a : ℝ} {φ : ℝ → ℝ} (hEig : IsRestrictedEigenfunction a φ)
    (hodd : Function.Odd φ) (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : ℂ → ℂ,
      DifferentiableOn ℂ A (Metric.ball (x : ℂ) r) ∧
      EqOn A (realCauchyExtension (height φ))
        (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) := by
  let Y := height φ
  let F := realCauchyExtension Y
  have hYc : Continuous Y := hEig.1.height_continuous
  obtain ⟨C, hYH⟩ := hEig.1.height_holder_half
  have hα : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hYzero : ∀ t : ℝ, 1 ≤ |t| → Y t = 0 := fun t ht => height_zero_of_one_le_abs φ ht
  have hFc : ContinuousOn F {z : ℂ | 0 ≤ z.im} := by
    simpa only [F, Y, upperHalfPlane, Complex.closure_setOf_lt_im] using
      realCauchyExtension_continuousOn hYH hα hYzero
  have hFd : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} :=
    (realCauchyExtension_diffContOnCl hYH hα hYzero).1
  let P := upperPrimitive F
  have hPc : Continuous P := upperPrimitive_continuous hFc
  have hPd (z : ℂ) (hz : 0 < z.im) : HasDerivAt P (F z) z := upperPrimitive_hasDerivAt hFc hFd hz
  obtain ⟨b, hb⟩ := hEig.height_Cauchy_boundary_hasDerivAt hodd
  let D : ℝ → ℝ := fun t => realCauchyBoundaryRe Y t + a * (P (t : ℂ)).im - b * t
  have hDd (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) : HasDerivAt D 0 t := by
    have hPim := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (upperPrimitive_boundary_hasDerivAt hFc t)
    change HasDerivAt (fun t : ℝ => (P (t : ℂ)).im) ((F (t : ℂ)).im) t at hPim
    have hFIm : (F (t : ℂ)).im = Y t := by simp [F, realCauchyExtension_ofReal]
    rw [hFIm] at hPim
    convert ((hb t ht).add (hPim.const_mul a)).sub ((hasDerivAt_id t).const_mul b) using 1
    all_goals (try funext u)
    all_goals (try dsimp only [D, Y, Pi.add_apply, Pi.sub_apply, id_eq])
    all_goals ring
  have hDconst (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) : D t = D 0 :=
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1 : ℝ) 1).isPreconnected
      (fun t ht => (hDd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hDd t ht).deriv) ht (by norm_num)
  let H : ℂ → ℂ := fun z => F z - (a : ℂ) * I * P z - (b : ℂ) * z - (D 0 : ℂ)
  have hHc : ContinuousOn H {z : ℂ | 0 ≤ z.im} := by
    exact ((hFc.sub (continuousOn_const.mul hPc.continuousOn)).sub
      (continuousOn_const.mul continuousOn_id)).sub continuousOn_const
  have hHd : DifferentiableOn ℂ H {z : ℂ | 0 < z.im} := by
    exact ((hFd.sub ((differentiableOn_const ((a : ℂ) * I)).mul
      (fun z hz => (hPd z hz).differentiableAt.differentiableWithinAt))).sub
      ((differentiableOn_const (b : ℂ)).mul differentiableOn_id)).sub (differentiableOn_const (D 0 : ℂ))
  have hHreal (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) : (H (t : ℂ)).re = 0 := by
    have h := hDconst t ht
    simp only [D, Complex.ofReal_zero, mul_zero, sub_zero] at h
    simp [H, F, D, realCauchyExtension_ofReal, mul_re, mul_im]
    linarith
  obtain ⟨r, hr, hBall⟩ := Metric.isOpen_iff.mp isOpen_Ioo x hx
  let Ω := Metric.ball (x : ℂ) r
  have hΩsym : MapsTo conj Ω Ω := by
    intro z hz
    simpa only [Ω, Metric.mem_ball, Complex.dist_conj_comm, Complex.conj_ofReal] using hz
  have hreal (z : ℂ) (hz : z ∈ Ω) (hz0 : z.im = 0) : (I * H z).im = 0 := by
    have hzr : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz0]
    have ht : z.re ∈ Ioo (-1 : ℝ) 1 := by
      apply hBall
      rw [hzr] at hz
      simpa only [Ω, Metric.mem_ball, Complex.isometry_ofReal.dist_eq] using hz
    rw [hzr]
    simpa only [mul_im, I_re, zero_mul, I_im, one_mul, zero_add] using hHreal z.re ht
  obtain ⟨K, hKd, hK⟩ := exists_differentiableOn_eqOn_of_symmetric Metric.isOpen_ball hΩsym
    ((continuousOn_const.mul hHc).mono inter_subset_right)
    (((differentiableOn_const I).mul hHd).mono inter_subset_right) hreal
  let B : ℂ → ℂ := fun z => -I * K z + (b : ℂ) * z + (D 0 : ℂ)
  have hBd : DifferentiableOn ℂ B Ω :=
    (((differentiableOn_const (-I)).mul hKd).add
      ((differentiableOn_const (b : ℂ)).mul differentiableOn_id)).add (differentiableOn_const (D 0 : ℂ))
  have hODE (z : ℂ) (hz : z ∈ Ω ∩ {z : ℂ | 0 < z.im}) :
      HasDerivAt P (((a : ℂ) * I) * P z + B z) z := by
    convert hPd z hz.2 using 1
    dsimp only [B]
    rw [show K z = I * H z from hK ⟨hz.1, (show 0 < z.im from hz.2).le⟩]
    dsimp only [H]
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_three]
    ring
  obtain ⟨Q, hQd, hQ, hQODE⟩ := exists_ode_extension_closed_upper_ball hr hBd hPc.continuousOn hODE
  let A : ℂ → ℂ := fun z => ((a : ℂ) * I) * Q z + B z
  refine ⟨r, hr, A, ((differentiableOn_const ((a : ℂ) * I)).mul hQd).add hBd, ?_⟩
  intro z hz
  dsimp only [A]
  rw [hQ hz]
  dsimp only [B]
  rw [show K z = I * H z from hK hz]
  dsimp only [H]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

/-- The original, canonically defined integrated height is real analytic
at every interior point, from the actual weak equation and oddness alone. -/
theorem IsRestrictedEigenfunction.height_analyticAt_of_odd
    {a : ℝ} {φ : ℝ → ℝ} (hEig : IsRestrictedEigenfunction a φ)
    (hodd : Function.Odd φ) (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    AnalyticAt ℝ (height φ) x := by
  obtain ⟨r, hr, A, hAd, hA⟩ := hEig.exists_height_Cauchy_extension_of_odd hodd x hx
  have hAa : AnalyticAt ℂ A (x : ℂ) := hAd.analyticAt (Metric.ball_mem_nhds _ hr)
  apply hAa.im_ofReal.congr
  filter_upwards [Metric.ball_mem_nhds x hr] with t ht
  have htC : (t : ℂ) ∈ Metric.ball (x : ℂ) r := by
    simpa only [Metric.mem_ball, Complex.isometry_ofReal.dist_eq] using ht
  have heq := congrArg Complex.im (hA ⟨htC, by simp⟩)
  simpa only [realCauchyExtension_ofReal, add_im, ofReal_im, mul_im,
    ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add] using heq

/-- Real analyticity of the actual height throughout the original open
interval, without any regular representative assumption on the datum. -/
theorem IsRestrictedEigenfunction.height_analyticOnNhd_of_odd
    {a : ℝ} {φ : ℝ → ℝ} (hEig : IsRestrictedEigenfunction a φ)
    (hodd : Function.Odd φ) : AnalyticOnNhd ℝ (height φ) (Ioo (-1 : ℝ) 1) :=
  fun x hx => hEig.height_analyticAt_of_odd hodd x hx

end Torsion.Spectral

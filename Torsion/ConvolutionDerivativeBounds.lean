module

public import Torsion.WeakHarmonicWeyl.ConvolutionEstimates
public import Torsion.WeakHarmonicWeyl.RadialKernel

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative derivatives of a fixed smoothing

The derivative of the actual weak-gradient convolution is another genuine
convolution, with the directional derivative of the scalar kernel. Its L²
Cauchy--Schwarz bound is uniform in the evaluation point.
-/

noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ENNReal ContDiff Convolution

namespace Torsion.WeakHarmonicRegularity

/-- Differentiate the fixed scalar smoothing kernel in an actual direction. -/
theorem fderiv_mollifyGradient_apply {g : Plane → Plane} {κ : Plane → ℝ}
    (hg : MemLp g 2 volume) (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    (x v : Plane) :
    fderiv ℝ (mollifyGradient g κ) x v =
      mollifyGradient g (fun z => fderiv ℝ κ z v) x := by
  let L : Plane →L[ℝ] ℝ →L[ℝ] Plane :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Plane →L[ℝ] Plane).flip
  have hderiv := hc.hasFDerivAt_convolution_right L
    (hg.locallyIntegrable (by norm_num)) (hκ.of_le (by simp)) x
  change fderiv ℝ (g ⋆[L, volume] κ) x v = _
  rw [hderiv.fderiv, convolution_precompR_apply L
    (hg.locallyIntegrable (by norm_num)) (hc.fderiv ℝ) (hκ.continuous_fderiv (by simp))]
  rfl

/-- Uniform directional Hessian control for the smoothed weak gradient. -/
theorem norm_fderiv_mollifyGradient_apply_le_L2
    {g : Plane → Plane} {κ : Plane → ℝ}
    (hg : MemLp g 2 volume) (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    (x v : Plane) :
    ‖fderiv ℝ (mollifyGradient g κ) x v‖ ≤
      (eLpNorm (fun z => fderiv ℝ κ z v) 2 volume).toReal *
        (eLpNorm g 2 volume).toReal := by
  have hdcont : Continuous (fun z => fderiv ℝ κ z v) :=
    (hκ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcompact : HasCompactSupport (fun z => fderiv ℝ κ z v) := hc.fderiv_apply ℝ v
  have hd : MemLp (fun z => fderiv ℝ κ z v) 2 volume :=
    hdcont.memLp_of_hasCompactSupport hcompact
  rw [fderiv_mollifyGradient_apply hg hκ hc]
  simpa only [Lp.norm_toLp] using norm_mollifyGradient_le_L2 hg hd x

/-- A smoothing at points of a ball uses only the weak field in a larger
fixed ball. This is a pointwise identity with the actual clipped field. -/
theorem mollifyGradient_eq_indicator_ball {g : Plane → Plane} {r : ℝ}
    (hr : 0 < r) {x : Plane} (hx : x ∈ Metric.ball 0 r) :
    mollifyGradient g (radialKernel r) x =
      mollifyGradient ((Metric.ball (0 : Plane) (2 * r)).indicator g) (radialKernel r) x := by
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    change radialKernel r (x - t) • g t =
      radialKernel r (x - t) • (Metric.ball (0 : Plane) (2 * r)).indicator g t
    by_cases ht : t ∈ Metric.ball (0 : Plane) (2 * r)
    · rw [indicator_of_mem ht]
    · have hκ : radialKernel r (x - t) = 0 := by
        by_contra hne
        have hxt : x - t ∈ Metric.ball (0 : Plane) r := by
          rw [← radialKernel_support hr]
          exact hne
        have hnormx : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
        have hnormxt : ‖x - t‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hxt
        apply ht
        apply Metric.mem_ball.mpr
        rw [dist_zero_right]
        have hh := norm_sub_le x (x - t)
        rw [sub_sub_cancel] at hh
        linarith
      simp [hκ]

/-- The derivative has the same localization, since the equality holds on
one full neighborhood of the evaluation point. -/
theorem fderiv_mollifyGradient_eq_indicator_ball {g : Plane → Plane} {r : ℝ}
    (hr : 0 < r) {x : Plane} (hx : x ∈ Metric.ball 0 r) :
    fderiv ℝ (mollifyGradient g (radialKernel r)) x =
      fderiv ℝ (mollifyGradient ((Metric.ball (0 : Plane) (2 * r)).indicator g)
        (radialKernel r)) x := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
  exact mollifyGradient_eq_indicator_ball hr hz

/-- Local L² control of the weak gradient suffices for a uniform directional
Hessian bound at every point of the smaller ball. -/
theorem norm_fderiv_mollifyGradient_apply_le_localL2
    {g : Plane → Plane} {r : ℝ} (hg : MemLp g 2 volume) (hr : 0 < r)
    {x : Plane} (hx : x ∈ Metric.ball 0 r) (v : Plane) :
    ‖fderiv ℝ (mollifyGradient g (radialKernel r)) x v‖ ≤
      (eLpNorm (fun z => fderiv ℝ (radialKernel r) z v) 2 volume).toReal *
        (eLpNorm ((Metric.ball (0 : Plane) (2 * r)).indicator g) 2 volume).toReal := by
  rw [fderiv_mollifyGradient_eq_indicator_ball hr hx]
  exact norm_fderiv_mollifyGradient_apply_le_L2
    (hg.indicator Metric.isOpen_ball.measurableSet)
    (radialKernel_contDiff r) (radialKernel_hasCompactSupport hr) x v

end Torsion.WeakHarmonicRegularity

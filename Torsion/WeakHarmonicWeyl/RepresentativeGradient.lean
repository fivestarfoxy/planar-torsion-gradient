module

public import Torsion.WeakHarmonicWeyl.MeanValue
public import Torsion.WeakHarmonicWeyl.RadialKernel
public import Torsion.WeakHarmonicWeyl.Associativity

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # A fixed local smooth representative of an actual weak harmonic gradient -/
noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ENNReal ContDiff Convolution

namespace Torsion.WeakHarmonicRegularity

theorem shrinkingBump_outer_tendsto :
    Tendsto (fun n : ℕ => (shrinkingBump n).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump, mul_one_div, mul_zero] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)

theorem mollifyGradient_eq_kernel_convolution (g : Plane → Plane) (κ : Plane → ℝ) :
    mollifyGradient g κ = κ ⋆[lsmul ℝ ℝ, volume] g := convolution_flip (lsmul ℝ ℝ)

private theorem mollifier_translated_tsupport (n : ℕ) (z : Plane) :
    tsupport (fun t => mollifier n (z - t)) ⊆
      Metric.closedBall z (shrinkingBump n).rOut := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro t ht
  have hmem : z - t ∈ Metric.ball (0 : Plane) (shrinkingBump n).rOut := by
    rw [← (shrinkingBump n).support_normed_eq (μ := volume)]
    exact ht
  apply Metric.mem_closedBall.mpr
  have hdist : dist t z < (shrinkingBump n).rOut := by
    simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using hmem
  exact hdist.le

private theorem mollified_harmonic_on_local_closedBall
    {U : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} {c x : Plane} {r : ℝ}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hw : IsWeakHarmonicOn U u g) (hr : 0 < r)
    (hball : Metric.ball c (4 * r) ⊆ U) (hx : x ∈ Metric.ball c r)
    (n : ℕ) (hn : (shrinkingBump n).rOut < r) :
    ∀ z ∈ Metric.closedBall x r, planarLaplacian (smoothApprox u n) z = 0 := by
  intro z hz
  apply mollify_laplacian_eq_zero hu hg hw
    (shrinkingBump n).contDiff_normed (shrinkingBump n).hasCompactSupport_normed
  intro t ht
  have htz := mollifier_translated_tsupport n z ht
  apply hball
  have htzd : dist t z ≤ (shrinkingBump n).rOut := Metric.mem_closedBall.mp htz
  have hzxd : dist z x ≤ r := Metric.mem_closedBall.mp hz
  have hxcd : dist x c < r := Metric.mem_ball.mp hx
  apply Metric.mem_ball.mpr
  have hd := dist_triangle t z c
  have hd' := dist_triangle z x c
  linarith

/-- On a smaller ball, an actual weak harmonic gradient agrees a.e. with
one fixed C∞ convolution. All stabilization and integrability steps are
proved: no a priori regularity of the weak representative is assumed. -/
theorem ae_eq_radial_mollifyGradient_on_ball
    {U : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} {c : Plane} {r : ℝ}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hw : IsWeakHarmonicOn U u g) (hr : 0 < r)
    (hball : Metric.ball c (4 * r) ⊆ U) :
    ∀ᵐ x ∂volume, x ∈ Metric.ball c r →
      g x = mollifyGradient g (radialKernel r) x := by
  have hlimr : ∀ᶠ n in atTop, (shrinkingBump n).rOut < r :=
    shrinkingBump_outer_tendsto.eventually (gt_mem_nhds hr)
  have hcont : Continuous (mollifyGradient g (radialKernel r)) :=
    (mollifyGradient_contDiff hg (radialKernel_contDiff r)
      (radialKernel_hasCompactSupport hr)).continuous
  filter_upwards [ae_gradient_smoothApprox_tendsto hu hg hw.1] with x hxlim
  intro hx
  have hlim := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (φ := shrinkingBump) shrinkingBump_outer_tendsto hcont x
  have hlim' : Tendsto
      (fun n => mollifyGradient (mollifyGradient g (radialKernel r)) (mollifier n) x)
      atTop (𝓝 (mollifyGradient g (radialKernel r) x)) := by
    simpa only [mollifyGradient_eq_kernel_convolution, mollifier] using hlim
  have heq : ∀ᶠ n in atTop,
      mollifyGradient (mollifyGradient g (radialKernel r)) (mollifier n) x =
        gradient (smoothApprox u n) x := by
    filter_upwards [hlimr] with n hn
    have hgrad : gradient (smoothApprox u n) = mollifyGradient g (mollifier n) :=
      funext fun y => (mollify_hasGradientAt hu hg hw.1
        (shrinkingBump n).contDiff_normed (shrinkingBump n).hasCompactSupport_normed y).gradient
    have hrep := smooth_harmonic_gradient_reproduce (smoothApprox_contDiff hu n) hr
      (mollified_harmonic_on_local_closedBall hu hg hw hr hball hx n hn)
    rw [hgrad] at hrep
    rw [mollifyGradient_commute (κ := radialKernel r) (ρ := mollifier n)
      hg (radialKernel_contDiff r).continuous
      (radialKernel_hasCompactSupport hr) (shrinkingBump n).continuous_normed
      (shrinkingBump n).hasCompactSupport_normed x, hrep, hgrad]
  exact tendsto_nhds_unique hxlim (hlim'.congr' heq)

theorem gradient_ae_eq_radial_mollifyGradient_on_ball
    {U : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} {c : Plane} {r : ℝ}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hw : IsWeakHarmonicOn U u g) (hr : 0 < r)
    (hball : Metric.ball c (4 * r) ⊆ U) :
    g =ᵐ[volume.restrict (Metric.ball c r)] mollifyGradient g (radialKernel r) := by
  filter_upwards [ae_restrict_of_ae
    (ae_eq_radial_mollifyGradient_on_ball hu hg hw hr hball),
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hmem
  exact hx hmem

/-- The fixed smooth gradient is the classical gradient of the fixed
smooth scalar convolution; this does not use a variable sequence of kernels. -/
theorem gradient_ae_eq_gradient_radial_mollify_on_ball
    {U : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} {c : Plane} {r : ℝ}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hw : IsWeakHarmonicOn U u g) (hr : 0 < r)
    (hball : Metric.ball c (4 * r) ⊆ U) :
    g =ᵐ[volume.restrict (Metric.ball c r)] gradient (mollify u (radialKernel r)) := by
  filter_upwards [gradient_ae_eq_radial_mollifyGradient_on_ball hu hg hw hr hball]
    with x hx
  exact hx.trans ((mollify_hasGradientAt hu hg hw.1 (radialKernel_contDiff r)
    (radialKernel_hasCompactSupport hr) x).gradient.symm)

end Torsion.WeakHarmonicRegularity

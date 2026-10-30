import Torsion.WeakHarmonicRegularity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Local constancy from an actually vanishing weak gradient

The concrete mollifications eventually have zero classical gradient on every
strictly smaller ball. They are constant there, and their almost-everywhere
limits identify one common constant for the original value class.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff Convolution

namespace Torsion
open WeakHarmonicRegularity

private theorem smoothApprox_gradient_eq_zero_of_small
    {u : Plane → ℝ} {g : Plane → Plane} (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hd : HasDistributionalGradient u g) {c : Plane} {R ρ : ℝ}
    (hzero : ∀ᵐ z ∂volume, z ∈ Metric.ball c R → g z = 0)
    (n : ℕ) (hn : (shrinkingBump n).rOut < R - ρ)
    {x : Plane} (hx : x ∈ Metric.ball c ρ) : gradient (smoothApprox u n) x = 0 := by
  rw [show gradient (smoothApprox u n) x = mollifyGradient g (mollifier n) x from
    (mollify_hasGradientAt hu hg hd (shrinkingBump n).contDiff_normed
      (shrinkingBump n).hasCompactSupport_normed x).gradient]
  change (∫ t, mollifier n (x - t) • g t) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [hzero] with t ht
  by_cases htR : t ∈ Metric.ball c R
  · simp only [ht htR, smul_zero, Pi.zero_apply]
  · have hκ : mollifier n (x - t) = 0 := by
      apply image_eq_zero_of_nmem_tsupport
      rw [mollifier, (shrinkingBump n).tsupport_normed_eq]
      intro hmem
      have hxt : ‖x - t‖ ≤ (shrinkingBump n).rOut := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hmem
      have hxc : ‖x - c‖ < ρ := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
      have htc : ‖t - c‖ ≤ ‖x - c‖ + ‖x - t‖ := by
        calc
          ‖t - c‖ = ‖(x - c) - (x - t)‖ := by congr 1; abel
          _ ≤ ‖x - c‖ + ‖x - t‖ := norm_sub_le _ _
      apply htR
      change dist t c < R
      rw [dist_eq_norm]
      linarith
    simp only [hκ, zero_smul, Pi.zero_apply]

/-- A distributional gradient that vanishes a.e. on a ball forces the value
to be one constant a.e. on every smaller concentric positive-radius ball.
All gradient, smoothing and convergence steps are actual proved statements. -/
theorem HasDistributionalGradient.ae_constant_on_smaller_ball
    {u : Plane → ℝ} {g : Plane → Plane} (hd : HasDistributionalGradient u g)
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume) {c : Plane} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hzero : g =ᵐ[volume.restrict (Metric.ball c R)] 0) :
    ∃ k : ℝ, u =ᵐ[volume.restrict (Metric.ball c ρ)] fun _ => k := by
  have hz : ∀ᵐ z ∂volume, z ∈ Metric.ball c R → g z = 0 :=
    (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hzero
  have hout : Tendsto (fun n : ℕ => (shrinkingBump n).rOut) atTop (𝓝 0) := by
    simpa only [shrinkingBump, mul_one_div, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hout.eventually (gt_mem_nhds (sub_pos.mpr hρR)))
  have hgrad (n : ℕ) (hn : N ≤ n) (x : Plane) (hx : x ∈ Metric.ball c ρ) :
      gradient (smoothApprox u n) x = 0 :=
    smoothApprox_gradient_eq_zero_of_small hu hg hd hz n (hN n hn) hx
  have hconst (n : ℕ) (hn : N ≤ n) {x y : Plane}
      (hx : x ∈ Metric.ball c ρ) (hy : y ∈ Metric.ball c ρ) :
      smoothApprox u n x = smoothApprox u n y := by
    apply (convex_ball c ρ).is_const_of_fderivWithin_eq_zero
      ((smoothApprox_contDiff hu n).differentiable (by simp)).differentiableOn ?_ hx hy
    intro z hzB
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hzB]
    ext v
    rw [fderiv_apply_eq_inner_gradient, hgrad n hn z hzB]
    simp
  have hlim := ae_smoothApprox_tendsto hu
  obtain ⟨x₀, hx₀, hx₀lim⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (Metric.isOpen_ball.measure_ne_zero volume (Metric.nonempty_ball.mpr hρ))
    (ae_restrict_of_ae hlim : ∀ᵐ x ∂volume.restrict (Metric.ball c ρ),
      Tendsto (fun n => smoothApprox u n x) atTop (𝓝 (u x)))
  refine ⟨u x₀, ?_⟩
  apply (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr
  filter_upwards [hlim] with x hx
  intro hxB
  have heq : (fun n => smoothApprox u n x) =ᶠ[atTop] (fun n => smoothApprox u n x₀) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hconst n hn hxB hx₀
  exact tendsto_nhds_unique hx ((tendsto_congr' heq).mpr hx₀lim)

end Torsion

module

public import Torsion.WeakHarmonicWeyl.Classical
public import Torsion.WeakHarmonicWeyl.RadialKernel
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Radial mean-value reproduction derived from the Cauchy formula -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Torsion.WeakHarmonicRegularity

private theorem polar_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  simp [circleMap, Complex.exp_mul_I]

private theorem integrable_polar_weight {f : ℂ → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      Complex.polarCoord.target := by
  have hcont : Continuous (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p)) :=
    continuous_fst.smul (hf.comp (by
      have heq : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
          (fun p : ℝ × ℝ => (p.1 : ℂ) *
            ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I)) :=
        funext Complex.polarCoord_symm_apply
      change Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
      rw [heq]
      fun_prop))
  refine ⟨hcont.aestronglyMeasurable.restrict, ?_⟩
  have hi : Integrable f (volume : Measure ℂ) := hf.integrable_of_hasCompactSupport hc
  have hp := Complex.lintegral_comp_polarCoord_symm (fun z => ‖f z‖ₑ)
  have heq : (∫⁻ p in Complex.polarCoord.target,
      ‖p.1 • f (Complex.polarCoord.symm p)‖ₑ) = ∫⁻ z, ‖f z‖ₑ := by
    rw [← hp]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem Complex.polarCoord.open_target.measurableSet] with p hp
    rw [enorm_smul, ← ofReal_norm_eq_enorm, Real.norm_of_nonneg hp.1.le]
    rfl
  change (∫⁻ p in Complex.polarCoord.target,
    ‖p.1 • f (Complex.polarCoord.symm p)‖ₑ) < ⊤
  rw [heq]
  exact hi.2

/-- Angular mean on the polar-coordinate interval. -/
theorem holomorphic_circle_mean_value_neg_pi {F : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ F (Metric.closedBall 0 r)) :
    (∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap 0 r θ)) =
      (2 * Real.pi : ℂ) * F 0 := by
  have hperiod : Function.Periodic (fun θ => F (circleMap 0 r θ)) (2 * Real.pi) :=
    (periodic_circleMap 0 r).comp F
  have hp := hperiod.intervalIntegral_add_eq (-Real.pi) 0
  have hmean := holomorphic_circle_mean_value hr hd
  have hinterval : (∫ θ in (-Real.pi)..Real.pi, F (circleMap 0 r θ)) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, F (circleMap 0 r θ) := by
    convert hp using 1 <;> congr 1 <;> ring
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    hinterval]
  exact hmean

/-- A compact radial scalar kernel reproduces a holomorphic function at the
origin. All measure and angular identities are proved from polar coordinates
and the Cauchy integral formula. -/
theorem holomorphic_radial_integral {F : ℂ → ℂ} {κ : ℂ → ℝ} {R : ℝ}
    (hF : Continuous F) (hκ : Continuous κ) (hc : HasCompactSupport κ)
    (hrad : ∀ z w, ‖z‖ = ‖w‖ → κ z = κ w)
    (hsupp : Function.support κ ⊆ Metric.closedBall 0 R)
    (hd : DifferentiableOn ℂ F (Metric.closedBall 0 R)) :
    (∫ z, κ z • F z) = (∫ z, κ z) • F 0 := by
  let f : ℂ → ℂ := fun z => κ z • F z
  let f₀ : ℂ → ℂ := fun z => κ z • F 0
  have hfc : Continuous f := hκ.smul hF
  have hf₀c : Continuous f₀ := hκ.smul continuous_const
  have hfs : HasCompactSupport f := hc.smul_right
  have hf₀s : HasCompactSupport f₀ := hc.smul_right
  rw [← Complex.integral_comp_polarCoord_symm f,
    ← integral_smul_const, ← Complex.integral_comp_polarCoord_symm f₀]
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • f (Complex.polarCoord.symm p) ∂(volume : Measure ℝ).prod volume) =
    (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • f₀ (Complex.polarCoord.symm p) ∂(volume : Measure ℝ).prod volume)
  rw [setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (s := Ioi (0 : ℝ)) (t := Ioo (-Real.pi) Real.pi)
      (f := fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (integrable_polar_weight hfc hfs),
    setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (s := Ioi (0 : ℝ)) (t := Ioo (-Real.pi) Real.pi)
      (f := fun p : ℝ × ℝ => p.1 • f₀ (Complex.polarCoord.symm p))
      (integrable_polar_weight hf₀c hf₀s)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change 0 < r at hr
  have hk (θ : ℝ) : κ (Complex.polarCoord.symm (r, θ)) = κ (r : ℂ) := by
    apply hrad
    rw [Complex.norm_polarCoord_symm]
    simp
  change (∫ θ in Ioo (-Real.pi) Real.pi,
    r • (κ (Complex.polarCoord.symm (r, θ)) • F (Complex.polarCoord.symm (r, θ)))) =
    (∫ θ in Ioo (-Real.pi) Real.pi,
    r • (κ (Complex.polarCoord.symm (r, θ)) • F 0))
  simp_rw [hk]
  by_cases hkr : κ (r : ℂ) = 0
  · simp only [hkr, zero_smul, smul_zero, integral_zero]
  have hrR : r ≤ R := by
    have hmem := hsupp hkr
    simpa [Metric.mem_closedBall, Real.norm_eq_abs, abs_of_pos hr] using hmem
  have hd' : DifferentiableOn ℂ F (Metric.closedBall 0 r) :=
    hd.mono (Metric.closedBall_subset_closedBall hrR)
  have hmean := holomorphic_circle_mean_value_neg_pi hr hd'
  simp_rw [polar_eq_circleMap]
  have hconst : (∫ θ in Ioo (-Real.pi) Real.pi, F 0) =
      (2 * Real.pi : ℂ) * F 0 := by
    simpa using holomorphic_circle_mean_value_neg_pi (F := fun _ => F 0) hr
      (differentiableOn_const (F 0))
  rw [integral_smul, integral_smul, integral_smul, integral_smul, hmean, hconst]

/-- The constructed normalized radial kernel reproduces a holomorphic field
on every closed ball where it is holomorphic. -/
theorem holomorphic_radialKernel_reproduce {F : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hF : Continuous F) (hr : 0 < r)
    (hd : DifferentiableOn ℂ F (Metric.closedBall c r)) :
    mollifyGradient F (radialKernel r) c = F c := by
  have hcomp : DifferentiableOn ℂ (fun z : ℂ => F (c - z))
      (Metric.closedBall 0 r) := by
    apply hd.comp ((differentiable_const c).sub differentiable_id).differentiableOn
    intro z hz
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left] using hz
  have heq := holomorphic_radial_integral
    (hF.comp (continuous_const.sub continuous_id))
    (radialKernel_contDiff r).continuous (radialKernel_hasCompactSupport hr)
    (fun z w hzw => radialKernel_radial r hzw)
    (by rw [radialKernel_support hr]; exact Metric.ball_subset_closedBall)
    hcomp
  rw [radialKernel_integral hr, one_smul] at heq
  simp only [Function.comp_apply, Pi.sub_apply, id_eq, sub_zero] at heq
  change (∫ t, radialKernel r (c - t) • F t) = F c
  calc
    _ = ∫ z, radialKernel r z • F (c - z) := by
      simpa only [sub_sub_cancel] using
        integral_sub_left_eq_self (fun z => radialKernel r z • F (c - z)) volume c
    _ = _ := heq

/-- A smooth harmonic function's actual gradient is unchanged by the fixed
normalized radial smoothing kernel. This is the stationary smoothing identity
used to identify a single smooth representative of a weak harmonic gradient. -/
theorem smooth_harmonic_gradient_reproduce {f : Plane → ℝ} {c : Plane} {r : ℝ}
    (hf : ContDiff ℝ ∞ f) (hr : 0 < r)
    (hh : ∀ z ∈ Metric.closedBall c r, planarLaplacian f z = 0) :
    mollifyGradient (gradient f) (radialKernel r) c = gradient f c := by
  have hcont : Continuous (complexGradient f) :=
    Complex.conjCLE.continuous.comp (gradient_contDiff hf).continuous
  have hdiff : DifferentiableOn ℂ (complexGradient f) (Metric.closedBall c r) :=
    fun z hz => (complexGradient_differentiableAt hf (hh z hz)).differentiableWithinAt
  have hrep := holomorphic_radialKernel_reproduce hcont hr hdiff
  have heq : mollifyGradient (complexGradient f) (radialKernel r) c =
      star (mollifyGradient (gradient f) (radialKernel r) c) := by
    change (∫ t, radialKernel r (c - t) • star (gradient f t)) =
      star (∫ t, radialKernel r (c - t) • gradient f t)
    simpa [Complex.star_def] using
      (integral_conj (f := fun t => radialKernel r (c - t) • gradient f t) (μ := volume))
  rw [heq] at hrep
  exact star_injective hrep

end Torsion.WeakHarmonicRegularity

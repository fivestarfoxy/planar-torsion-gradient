module

public import Torsion.MarkedFluxDifferentiation

@[expose] public section

/-! # A boundary derivative estimate from local harmonic values

For a Sobolev field with zero trace on the flat boundary, the actual inward
quotient on a harmonic half-ball is bounded by the L² norm of its values on
that half-ball. The constant depends only on its radius. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Torsion
open WeakHarmonicRegularity

set_option backward.isDefEq.respectTransparency false

private def radialNormalTest (r : ℝ) (z : Plane) : ℝ :=
  fderiv ℝ (radialKernel r) z Complex.I

private theorem memLp_radialNormalTest {r : ℝ} (hr : 0 < r) :
    MemLp (radialNormalTest r) 2 volume :=
  (((radialKernel_contDiff r).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    ((radialKernel_hasCompactSupport hr).fderiv_apply ℝ Complex.I)

private theorem radialNormalTest_zero {r : ℝ} (hr : 0 < r) {z : Plane}
    (hz : z ∉ Metric.closedBall 0 r) : radialNormalTest r z = 0 := by
  unfold radialNormalTest
  rw [fderiv_of_notMem_tsupport ℝ (by simpa only [radialKernel_tsupport hr] using hz)]
  rfl

/-- Weak integration by parts transfers the fixed-kernel flux from the weak
gradient to the oscillation of the derivative of the kernel under reflection. -/
private theorem markedGradientFlux_eq_value_pairing {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 upperHalfPlane u g) {r : ℝ} (hr : 0 < r) :
    markedGradientFlux r g =
      ∫ z : Plane, u z * (radialNormalTest r (star z) - radialNormalTest r z) := by
  let w : Plane → ℝ := fun z => u z - reflectedValue u z
  let h : Plane → Plane := fun z => g z - reflectedGradient g z
  have hmem : MemH10 univ w h :=
    (hu.mono (subset_univ _)).sub (hu.reflectedValue.mono (subset_univ _))
  have hκ := radialKernel_contDiff r
  have hcompact := radialKernel_hasCompactSupport hr
  have hm := memLp_radialNormalTest hr
  have hi : Integrable (fun t => radialKernel r t • h t) :=
    memLp_one_iff_integrable.mp ((hκ.continuous.memLp_of_hasCompactSupport (p := 2) hcompact).smul hmem.2.1)
  have hinner (v : Plane) : inner (𝕜 := ℝ) v Complex.I = v.im := by
    simp [Complex.inner, Complex.mul_re]
  have hflux : markedGradientFlux r g = ∫ t, inner (𝕜 := ℝ) (h t) Complex.I * radialKernel r t := by
    change (∫ t, radialKernel r (0 - t) • h t).im = _
    have heven (t : Plane) : radialKernel r (0 - t) = radialKernel r t :=
      radialKernel_radial _ (by simp)
    simp_rw [heven]
    calc
      _ = ∫ t, (radialKernel r t • h t).im := (integral_im hi).symm
      _ = _ := integral_congr_ae (ae_of_all _ fun t => by simp [hinner, mul_comm])
  have hweak := hmem.distributionalGradient (radialKernel r) hκ hcompact Complex.I
  have hneg : markedGradientFlux r g = -(∫ t, w t * radialNormalTest r t) := by
    rw [hflux]
    change (∫ t, w t * radialNormalTest r t) = -_ at hweak
    linarith
  have hchange : (∫ t, reflectedValue u t * radialNormalTest r t) =
      ∫ t, u t * radialNormalTest r (star t) := by
    simpa only [reflectedValue, star_star] using
      integral_comp_conjugation (fun t => u t * radialNormalTest r (star t))
  rw [hneg]
  simp only [w, sub_mul, mul_sub]
  have h1 : Integrable (fun z => u z * radialNormalTest r z) := hu.1.integrable_mul hm
  have h2 : Integrable (fun z => reflectedValue u z * radialNormalTest r z) :=
    (memLp_reflectedValue hu.1).integrable_mul hm
  have h3 : Integrable (fun z => u z * radialNormalTest r (star z)) :=
    hu.1.integrable_mul (memLp_reflectedValue hm)
  rw [integral_sub h1 h2, hchange, integral_sub h3 h1]
  ring

private theorem exists_halfBall_kernel_L2_bound {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : Plane → ℝ} {g : Plane → Plane},
      MemH10 upperHalfPlane u g → |markedGradientFlux (ρ / 4) g| ≤
        C * (eLpNorm u 2 (volume.restrict (upperHalfPlane ∩ Metric.ball 0 ρ))).toReal := by
  let r := ρ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let S := upperHalfPlane ∩ Metric.ball (0 : Plane) ρ
  have hU : MeasurableSet upperHalfPlane := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hS : MeasurableSet S := hU.inter Metric.isOpen_ball.measurableSet
  let K := fun z => radialNormalTest r (star z) - radialNormalTest r z
  have hK : MemLp K 2 volume := (memLp_reflectedValue (memLp_radialNormalTest hr)).sub (memLp_radialNormalTest hr)
  refine ⟨‖hK.toLp K‖, norm_nonneg _, ?_⟩
  intro u g hu
  rw [markedGradientFlux_eq_value_pairing hu hr]
  have hind : (∫ z : Plane, u z * K z) = ∫ z : Plane, K z • S.indicator u z := by
    apply integral_congr_ae
    have hzero := (ae_restrict_iff' hU.compl).mp hu.value_ae_zero_off
    filter_upwards [hzero] with z hz
    by_cases hi : z ∈ S
    · simp [indicator_of_mem hi, smul_eq_mul, mul_comm]
    · rw [indicator_of_notMem hi, smul_zero]
      by_cases hU' : z ∈ upperHalfPlane
      · have hz' : ρ ≤ ‖z‖ := by
          by_contra! h
          exact hi ⟨hU', by simpa only [Metric.mem_ball, dist_zero_right] using h⟩
        have hball : z ∉ Metric.closedBall 0 r := by
          simp only [Metric.mem_closedBall, dist_zero_right, not_le]
          dsimp [r]
          linarith
        have hstar : star z ∉ Metric.closedBall 0 r := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hball
        change u z * (radialNormalTest r (star z) - radialNormalTest r z) = 0
        rw [radialNormalTest_zero hr hstar, radialNormalTest_zero hr hball, sub_self, mul_zero]
      · simp [hz hU']
  change |∫ z, u z * K z| ≤ _
  rw [hind, ← Real.norm_eq_abs]
  have hI : MemLp (S.indicator u) 2 volume := hu.1.indicator hS
  have hl := norm_integral_smul_le_L2 hK hI
  rw [Lp.norm_toLp (S.indicator u) hI, eLpNorm_indicator_eq_eLpNorm_restrict hS] at hl
  exact hl

/-- Manuscript estimate (4.7) for the genuine inward quotient of a continuous
local representative. The norm only uses values on the indicated half-ball. -/
theorem exists_halfBall_normal_flux_L2_bound {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : Plane → ℝ} {g : Plane → Plane} {q : ℝ},
      MemH10 upperHalfPlane u g →
      IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 ρ) u g →
      ContinuousOn u (upperHalfPlane ∩ Metric.ball 0 ρ) → HasMarkedFlux u q →
      |q| ≤ C * (eLpNorm u 2 (volume.restrict (upperHalfPlane ∩ Metric.ball 0 ρ))).toReal := by
  obtain ⟨C, hC, hbound⟩ := exists_halfBall_kernel_L2_bound hρ
  refine ⟨C, hC, ?_⟩
  intro u g q hu hw hc hq
  have hr : 0 < ρ / 4 := by positivity
  rw [hq.eq_fixedGradientKernel hu (by simpa only [show 4 * (ρ / 4) = ρ by ring] using hw) hr hρ hc]
  exact hbound hu

/-- For a weak harmonic zero-flat-trace value, a smooth odd harmonic reflection
exists near the mark and its *classical* normal derivative satisfies (4.7).
Neither a continuous representative nor a boundary derivative is an input. -/
theorem exists_halfBall_smooth_odd_harmonic_L2_bound {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : Plane → ℝ} {g : Plane → Plane},
      MemH10 upperHalfPlane u g →
      IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 ρ) u g →
      ∃ v : Plane → ℝ, ContDiff ℝ ∞ v ∧
        (u =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 (ρ / 8))] v) ∧
        (∀ z ∈ Metric.ball 0 (ρ / 8), v (star z) = -v z) ∧
        (∀ z ∈ Metric.ball 0 (ρ / 8), planarLaplacian v z = 0) ∧
        |(gradient v 0).im| ≤ C *
          (eLpNorm u 2 (volume.restrict (upperHalfPlane ∩ Metric.ball 0 ρ))).toReal := by
  obtain ⟨C, hC, hbound⟩ := exists_halfBall_kernel_L2_bound hρ
  refine ⟨C, hC, ?_⟩
  intro u g hu hw
  let r := ρ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrho : 4 * r = ρ := by dsimp [r]; ring
  have hsmall : r / 2 = ρ / 8 := by dsimp [r]; ring
  let w : Plane → ℝ := fun z => u z - reflectedValue u z
  let h : Plane → Plane := fun z => g z - reflectedGradient g z
  have hm : MemH10 univ w h := (hu.mono (subset_univ _)).sub (hu.reflectedValue.mono (subset_univ _))
  have hw' : IsWeakHarmonicOn (Metric.ball 0 (4 * r)) w h := by
    rw [hrho]
    exact hw.odd_reflection hu
  obtain ⟨v, hv, hAE, hG, hh⟩ := hw'.exists_smooth_harmonicRepresentative_on_ball hm hr Subset.rfl
  have hodd (z : Plane) : w (star z) = -w z := by simp [w, reflectedValue]
  have hupper : w =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 (r / 2))] u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hu.odd_reflection_ae_upper
  have hnear : u =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 (r / 2))] v :=
    hupper.symm.trans (ae_restrict_of_ae_restrict_of_subset inter_subset_right hAE)
  rw [← hsmall]
  refine ⟨v, hv, hnear, antisymmetric_of_continuous_ae_odd_on_ball hv.continuous.continuousOn hAE hodd,
    hh, ?_⟩
  have hkernel := gradient_ae_eq_radial_mollifyGradient_on_ball hm.1 hm.2.1 hw' hr Subset.rfl
  have hGs : gradient v =ᵐ[volume.restrict (Metric.ball 0 (r / 2))]
      mollifyGradient h (radialKernel r) :=
    hG.symm.trans (ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_ball (half_le_self hr.le)) hkernel)
  have heq := Measure.eqOn_open_of_ae_eq hGs Metric.isOpen_ball
    (gradient_contDiff hv).continuous.continuousOn
    (mollifyGradient_contDiff hm.2.1 (radialKernel_contDiff r) (radialKernel_hasCompactSupport hr)).continuous.continuousOn
  rw [heq (Metric.mem_ball_self (half_pos hr))]
  exact hbound hu

/-- On one half-ball, strong L² convergence of the *values* of harmonic fields
with zero flat trace gives numerical convergence of their inward quotients. -/
theorem markedFlux_tendsto_of_local_L2_values {ρ : ℝ} (hρ : 0 < ρ)
    {u : ℕ → Plane → ℝ} {g : ℕ → Plane → Plane} {q : ℕ → ℝ}
    {v : Plane → ℝ} {h : Plane → Plane} {p : ℝ}
    (hu : ∀ n, MemH10 upperHalfPlane (u n) (g n))
    (hw : ∀ n, IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 ρ) (u n) (g n))
    (hc : ∀ n, ContinuousOn (u n) (upperHalfPlane ∩ Metric.ball 0 ρ))
    (hq : ∀ n, HasMarkedFlux (u n) (q n))
    (hv : MemH10 upperHalfPlane v h) (hh : IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 ρ) v h)
    (hvc : ContinuousOn v (upperHalfPlane ∩ Metric.ball 0 ρ)) (hp : HasMarkedFlux v p)
    (hlim : Tendsto (fun n => eLpNorm (fun z => u n z - v z) 2
      (volume.restrict (upperHalfPlane ∩ Metric.ball 0 ρ))) atTop (𝓝 0)) :
    Tendsto q atTop (𝓝 p) := by
  obtain ⟨C, _, hbound⟩ := exists_halfBall_normal_flux_L2_bound hρ
  have hdiff (n : ℕ) : IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 ρ)
      (fun z => u n z - v z) (fun z => g n z - h z) := by
    refine ⟨((hu n).sub hv).distributionalGradient, ?_⟩
    intro ψ hψ
    have h1 := integrable_real_inner_of_memLp_two (hu n).2.1 (hψ.memLp_gradient (p := 2))
    have h2 := integrable_real_inner_of_memLp_two hv.2.1 (hψ.memLp_gradient (p := 2))
    simp only [inner_sub_left]
    rw [integral_sub h1 h2, (hw n).2 ψ hψ, hh.2 ψ hψ, sub_self]
  have hval := (ENNReal.continuousAt_toReal (ENNReal.zero_ne_top)).tendsto.comp hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n =>
    hbound ((hu n).sub hv) (hdiff n) ((hc n).sub hvc) ((hq n).sub hp))
  simpa only [Function.comp_def, ENNReal.toReal_zero, mul_zero] using hval.const_mul C

end Torsion

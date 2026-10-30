import Torsion.MarkedFlux
import Torsion.WeakHarmonicWeyl.ConvolutionEstimates

/-!
# Fixed-ball representation of genuine marked flux

Odd weak reflection and the actual radial Weyl representative make the
marked derivative a fixed integral of the weak gradient. This public
interface is used to differentiate marked flux from strong H¹ convergence.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion
open WeakHarmonicRegularity

/-- The fixed radial-kernel functional of an actual zero-flat-trace weak
gradient. Its agreement with the true inward quotient is proved below. -/
def markedGradientFlux (r : ℝ) (g : Plane → Plane) : ℝ :=
  (mollifyGradient (fun z => g z - reflectedGradient g z) (radialKernel r) 0).im

/-- The functional depends only on the actual a.e. weak-gradient class. -/
theorem markedGradientFlux_congr_ae {g h : Plane → Plane}
    (hgh : g =ᵐ[volume] h) (r : ℝ) :
    markedGradientFlux r g = markedGradientFlux r h := by
  have href := measurePreserving_conjugation.quasiMeasurePreserving.ae hgh
  unfold markedGradientFlux
  congr 1
  apply integral_congr_ae
  filter_upwards [hgh, href] with z hz hzr
  simp only [reflectedGradient, hz, hzr]

/-- One fixed ball suffices for marked flux: changes to the weak gradient
outside the kernel ball have no effect, including on the reflected side. -/
theorem markedGradientFlux_eq_of_ae_eq_on_ball {g h : Plane → Plane} {r : ℝ}
    (hr : 0 < r) (hgh : g =ᵐ[volume.restrict (Metric.ball 0 r)] h) :
    markedGradientFlux r g = markedGradientFlux r h := by
  have hglobal : ∀ᵐ z ∂volume, z ∈ Metric.ball (0 : Plane) r → g z = h z :=
    (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hgh
  have href := measurePreserving_conjugation.quasiMeasurePreserving.ae hglobal
  unfold markedGradientFlux
  congr 1
  apply integral_congr_ae
  filter_upwards [hglobal, href] with z hz hzr
  by_cases hzB : z ∈ Metric.ball (0 : Plane) r
  · have hzstar : star z ∈ Metric.ball (0 : Plane) r := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_star] using hzB
    simp only [reflectedGradient, hz hzB, hzr hzstar]
  · have hker : radialKernel r (-z) = 0 := by
      by_contra hne
      have hsupport : -z ∈ Function.support (radialKernel r) := hne
      rw [radialKernel_support hr] at hsupport
      apply hzB
      simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using hsupport
    simp [hker]

private theorem halfBall_open (r : ℝ) : IsOpen (upperHalfPlane ∩ Metric.ball (0 : Plane) r) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball

private theorem markedFlux_of_smooth {v : Plane → ℝ} (hv : ContDiff ℝ ∞ v)
    (hv0 : v 0 = 0) : HasMarkedFlux v (gradient v 0).im := by
  have hline : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const Complex.I
  have hdv : HasFDerivAt v (fderiv ℝ v 0) ((0 : ℂ) * Complex.I) := by
    simpa using (hv.differentiable (by simp) 0).hasFDerivAt
  have hd : HasDerivAt (fun t : ℝ => v ((t : ℂ) * Complex.I)) (gradient v 0).im 0 := by
    convert hdv.comp_hasDerivAt 0 hline using 1
    simp [fderiv_apply_eq_inner_gradient, Complex.inner, Complex.mul_re]
  exact hasMarkedFlux_of_normal_derivative hv0 hd

/-- Every actual weakly harmonic zero-trace half-ball pair with its continuous
local representative has a genuine inward flux, equal to a fixed gradient integral. -/
theorem markedGradientFlux_isMarkedFlux
    {u : Plane → ℝ} {g : Plane → Plane} {r s : ℝ}
    (hu : MemH10 upperHalfPlane u g)
    (hw : IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 (4 * r)) u g)
    (hr : 0 < r) (hs : 0 < s)
    (hc : ContinuousOn u (upperHalfPlane ∩ Metric.ball 0 s)) :
    HasMarkedFlux u (markedGradientFlux r g) := by
  let w : Plane → ℝ := fun z => u z - reflectedValue u z
  let h : Plane → Plane := fun z => g z - reflectedGradient g z
  have hmem : MemH10 univ w h :=
    (hu.mono (subset_univ _)).sub (hu.reflectedValue.mono (subset_univ _))
  have hweak : IsWeakHarmonicOn (Metric.ball 0 (4 * r)) w h := hw.odd_reflection hu
  obtain ⟨v, hv, hAE, hG⟩ := hweak.exists_smoothRepresentative_on_ball hmem hr Subset.rfl
  have hodd : ∀ z, w (star z) = -w z := by
    intro z
    simp only [w, reflectedValue, star_star]
    ring
  have hv0 := zero_at_origin_of_continuous_ae_odd_on_ball (half_pos hr)
    hv.continuous.continuousOn hAE hodd
  have hflux := markedFlux_of_smooth hv hv0
  have hker := gradient_ae_eq_radial_mollifyGradient_on_ball
    hmem.1 hmem.2.1 hweak hr Subset.rfl
  have hGsmall : gradient v =ᵐ[volume.restrict (Metric.ball 0 (r / 2))]
      mollifyGradient h (radialKernel r) :=
    hG.symm.trans (ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_ball (half_le_self hr.le)) hker)
  have hpointG := Measure.eqOn_open_of_ae_eq hGsmall Metric.isOpen_ball
    (gradient_contDiff hv).continuous.continuousOn
    (mollifyGradient_contDiff hmem.2.1 (radialKernel_contDiff r)
      (radialKernel_hasCompactSupport hr)).continuous.continuousOn
  have hG0 := hpointG (Metric.mem_ball_self (half_pos hr))
  let a : ℝ := min s (r / 2)
  have ha : 0 < a := lt_min hs (half_pos hr)
  have hsmallH : upperHalfPlane ∩ Metric.ball (0 : Plane) a ⊆ upperHalfPlane :=
    inter_subset_left
  have hsmallB : upperHalfPlane ∩ Metric.ball (0 : Plane) a ⊆
      Metric.ball 0 (r / 2) :=
    inter_subset_right.trans (Metric.ball_subset_ball (min_le_right _ _))
  have hsmallS : upperHalfPlane ∩ Metric.ball (0 : Plane) a ⊆
      upperHalfPlane ∩ Metric.ball 0 s :=
    inter_subset_inter_right _ (Metric.ball_subset_ball (min_le_left _ _))
  have hUpper : w =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 a)] u :=
    ae_restrict_of_ae_restrict_of_subset hsmallH hu.odd_reflection_ae_upper
  have hSmall : w =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 a)] v :=
    ae_restrict_of_ae_restrict_of_subset hsmallB hAE
  have hEq : u =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 a)] v :=
    hUpper.symm.trans hSmall
  have hpoint := Measure.eqOn_open_of_ae_eq hEq (halfBall_open a)
    (hc.mono hsmallS) hv.continuous.continuousOn
  have hqu : HasMarkedFlux u (gradient v 0).im := by
    apply hflux.congr'
    filter_upwards [eventually_vertical_mem_halfBall ha] with t ht
    rw [hpoint ht]
  simpa only [hG0, markedGradientFlux, h] using hqu


/-- A supplied genuine marked flux agrees with the constructed fixed-ball
gradient functional; no boundary-gradient convergence premise is used. -/
theorem HasMarkedFlux.eq_fixedGradientKernel
    {u : Plane → ℝ} {g : Plane → Plane} {r s q : ℝ}
    (hq : HasMarkedFlux u q) (hu : MemH10 upperHalfPlane u g)
    (hw : IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 (4 * r)) u g)
    (hr : 0 < r) (hs : 0 < s)
    (hc : ContinuousOn u (upperHalfPlane ∩ Metric.ball 0 s)) :
    q = markedGradientFlux r g :=
  hq.unique (markedGradientFlux_isMarkedFlux hu hw hr hs hc)

end Torsion

module

public import Torsion.CauchyImageArea
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Torsion.WeakHarmonicWeyl.Classical

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Circular means and area for the conformal torsion comparison -/

noncomputable section
open Set Metric MeasureTheory
namespace Torsion.Spectral

/-- Angular mean of the torsion expression on a holomorphic coordinate disk.
Adding one quarter of the squared distance leaves a harmonic function. -/
theorem conformal_deflection_mean {F A : Plane → Plane} {P : Plane → ℝ} {r : ℝ} (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F (closedBall 0 r)) (hA : AnalyticOnNhd ℂ A (closedBall 0 r))
    (hP : ∀ z ∈ closedBall (0 : Plane) r, P z = -(F z).im ^ 2 / 2 + (A z).im) :
    (2 * Real.pi) * P 0 =
      (∫ θ in (-Real.pi)..Real.pi, P (circleMap 0 r θ)) +
        (∫ θ in (-Real.pi)..Real.pi, ‖F (circleMap 0 r θ) - F 0‖ ^ 2) / 4 := by
  let H (z : Plane) := F z ^ 2 / 4 - star (F 0) * F z / 2 +
    ((‖F 0‖ ^ 2 : ℝ) : Plane) / 4 - Complex.I * A z
  have hH : AnalyticOnNhd ℂ H (closedBall 0 r) := by
    intro z hz
    dsimp [H]
    have hf := hF z hz
    have ha := hA z hz
    fun_prop
  have he (z : Plane) (hz : z ∈ closedBall 0 r) :
      (H z).re = P z + ‖F z - F 0‖ ^ 2 / 4 := by
    rw [hP z hz]
    dsimp only [H]
    rw [← Complex.normSq_eq_norm_sq (F 0), ← Complex.normSq_eq_norm_sq (F z - F 0)]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im, pow_two]
    ring
  have hmean := WeakHarmonicRegularity.holomorphic_circle_mean_value hr hH.differentiableOn
  have hperiod : Function.Periodic (fun θ => H (circleMap 0 r θ)) (2 * Real.pi) :=
    (periodic_circleMap 0 r).comp H
  have hshift := hperiod.intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add, hmean] at hshift
  have hm (θ : ℝ) : circleMap 0 r θ ∈ closedBall (0:Plane) r :=
    sphere_subset_closedBall (circleMap_mem_sphere 0 hr.le θ)
  have hcont {g : Plane → Plane} (hg : AnalyticOnNhd ℂ g (closedBall 0 r)) :
      Continuous (fun θ => g (circleMap 0 r θ)) :=
    hg.continuousOn.comp_continuous (by fun_prop) hm
  have hi := Complex.reCLM.intervalIntegral_comp_comm (μ:=volume) (a := -Real.pi) (b := Real.pi)
    ((hcont hH).intervalIntegrable _ _)
  change (∫ θ in (-Real.pi)..Real.pi, (H (circleMap 0 r θ)).re) = _ at hi
  rw [hshift] at hi
  have hcoord (θ : ℝ) := he _ (hm θ)
  simp_rw [hcoord] at hi
  have hPc : Continuous (fun θ => P (circleMap 0 r θ)) := by
    have eq : (fun θ => P (circleMap 0 r θ)) = fun θ =>
        -(F (circleMap 0 r θ)).im^2 / 2 + (A (circleMap 0 r θ)).im :=
      funext fun θ => hP _ (hm θ)
    rw [eq]
    exact (((Complex.continuous_im.comp (hcont hF)).pow 2).neg.div_const 2).add
      (Complex.continuous_im.comp (hcont hA))
  have hn : Continuous (fun θ => ‖F (circleMap 0 r θ) - F 0‖^2 / 4) :=
    (((hcont hF).sub continuous_const).norm.pow 2).div_const 4
  rw [intervalIntegral.integral_add (hPc.intervalIntegrable _ _) (hn.intervalIntegrable _ _),
    intervalIntegral.integral_div] at hi
  have h₀ := he 0 (mem_closedBall_self hr.le)
  simp only [sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,add_zero] at h₀
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, add_zero, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero] at hi
  rw [h₀] at hi
  exact hi.symm

/-- The usual angular integral over the centered period gives the same
circle average as the interval starting at zero. -/
theorem angular_integral_eq_circleAverage (P : Plane → ℝ) (r : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, P (circleMap 0 r θ)) =
      (2 * Real.pi) * Real.circleAverage P 0 r := by
  have hp := ((periodic_circleMap 0 r).comp P).intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at hp
  simp only [Function.comp_apply] at hp
  rw [hp, Real.circleAverage_def, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul]

/-- Every conformal subdisk contributes at most the physical image's
Euclidean area to the Jacobian integral. -/
theorem conformal_disk_energy_le_area {F : Plane → Plane} {r : ℝ} {D : Set Plane}
    (hF : AnalyticOnNhd ℂ F (ball 0 r)) (hinj : InjOn F (ball 0 r))
    (hmaps : MapsTo F (ball 0 r) D) (hfinite : volume D ≠ ⊤) :
    (∫ z in ball (0 : Plane) r, ‖deriv F z‖ ^ 2) ≤ (volume D).toReal := by
  have hj := integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball
    (fun z hz => (hF z hz).differentiableAt.hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt)
    hinj (fun _ : Plane => (1 : ℝ))
  have heq : (volume (F '' ball (0 : Plane) r)).toReal = ∫ z in ball (0:Plane) r, ‖deriv F z‖ ^ 2 := by
    simpa only [complex_mul_real_det, abs_sq, smul_eq_mul, mul_one, integral_const,
      measureReal_def, Measure.restrict_apply_univ] using hj
  rw [← heq]
  exact ENNReal.toReal_mono hfinite (measure_mono hmaps.image_subset)

end Torsion.Spectral

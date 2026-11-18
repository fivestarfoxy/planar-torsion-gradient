module

public import Torsion.Proof.PaperRadialArea
public import Torsion.Proof.PaperRadialGreen

@[expose] public section

/-! # The divergence theorem on a smooth planar radial frame -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Torsion

def radialFrameCurve (c : Plane) (R : ℝ → ℝ) (θ : ℝ) : Plane :=
  c + circleMap 0 (R θ) θ

theorem radialFrameCurve_contDiff (c : Plane) {R : ℝ → ℝ} (hR : ContDiff ℝ 1 R) :
    ContDiff ℝ 1 (radialFrameCurve c R) := by
  change ContDiff ℝ 1 (fun θ : ℝ => c + (0 + Complex.ofRealCLM (R θ) *
    Complex.exp (Complex.ofRealCLM θ * Complex.I)))
  fun_prop

private theorem radialFrameCurve_trig (c : Plane) (R : ℝ → ℝ) (t : ℝ) :
    radialFrameCurve c R t = c + ((R t * Real.cos t : ℝ) : ℂ) +
      ((R t * Real.sin t : ℝ) : ℂ) * Complex.I := by
  simp [radialFrameCurve, circleMap, Complex.exp_mul_I]
  ring

theorem radialFrameCurve_cross (c : Plane) {R : ℝ → ℝ} (hR : ContDiff ℝ 1 R) (t : ℝ) :
    planarCross (radialFrameCurve c R t - c) (deriv (radialFrameCurve c R) t) = R t ^ 2 := by
  have hr := ((hR.differentiable (by decide)) t).hasDerivAt
  have hv := (((hr.mul (Real.hasDerivAt_cos t)).ofReal_comp.const_add c).add
    ((hr.mul (Real.hasDerivAt_sin t)).ofReal_comp.mul_const Complex.I)).deriv
  have hf : radialFrameCurve c R = fun x => c + ((R x * Real.cos x : ℝ) : ℂ) +
      ((R x * Real.sin x : ℝ) : ℂ) * Complex.I := funext (radialFrameCurve_trig c R)
  rw [hf]
  change planarCross _ (deriv (fun x => _) t) = _
  rw [show deriv (fun x => c + ((R x * Real.cos x : ℝ) : ℂ) +
      ((R x * Real.sin x : ℝ) : ℂ) * Complex.I) t = _ from hv]
  simp [planarCross, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re]
  linear_combination (R t)^2 * Real.sin_sq_add_cos_sq t

theorem radialFrameCurve_speed_pos (c : Plane) {R : ℝ → ℝ} (hR : ContDiff ℝ 1 R)
    (hpos : ∀ θ, 0 < R θ) (t : ℝ) : 0 < ‖deriv (radialFrameCurve c R) t‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have h := radialFrameCurve_cross c hR t
  rw [hz] at h
  simp [planarCross] at h
  exact (sq_pos_of_pos (hpos t)).ne h

theorem radialFrameCurve_closed (c : Plane) {R : ℝ → ℝ} (he : R (-Real.pi) = R Real.pi) :
    radialFrameCurve c R (-Real.pi) = radialFrameCurve c R Real.pi := by
  simp [radialFrameCurve_trig, he]

/-- For a frame described by polar radius about an interior point, the
integral of divergence against planar Lebesgue measure equals the
oriented integral along the actual frame. -/
theorem smooth_radial_frame_divergence (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ)) {W : Plane → Plane} (hW : ContDiff ℝ 1 W) :
    (∫ z in D.carrier, Shape.divergence W z) = ∫ θ in (-Real.pi)..Real.pi,
      planarCross (W (radialFrameCurve c R θ)) (deriv (radialFrameCurve c R) θ) := by
  have hd := hW.continuous_fderiv (by decide)
  have hc : Continuous (Shape.divergence W) :=
    (Complex.continuous_re.comp (hd.clm_apply continuous_const)).add
    (Complex.continuous_im.comp (hd.clm_apply continuous_const))
  have hi : IntegrableOn (Shape.divergence W) D.carrier := (hc.continuousOn.integrableOn_compact D.bounded.isCompact_closure).mono_set subset_closure
  rw [integral_radial_frame c R D.isOpen.measurableSet hi (fun θ _ => hpos θ) hmem]
  have h := radialFrame_divergence c (radialFrameCurve c R) W (-Real.pi) Real.pi (radialFrameCurve_contDiff c hR) hW (radialFrameCurve_closed c hend)
  simp_rw [radialFrameCurve_cross c hR] at h
  simpa only [radialFrameCurve, add_sub_cancel_left] using h

end Torsion

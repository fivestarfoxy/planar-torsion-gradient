module

public import Torsion.Proof.PaperSmoothFrame
public import Torsion.SobolevLocalization
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

/-! # Signed boundary area of a holomorphic disk map

The positively oriented cross-product integral counts area with multiplicity
and is twice the integral of the actual holomorphic Jacobian. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion

private def holomorphicAreaField (F : Plane → Plane) (z : Plane) : Plane :=
  F z * star (deriv F z)

private theorem holomorphicAreaField_divergence {U : Set Plane} (hU : IsOpen U)
    {F : Plane → Plane} (hF : DifferentiableOn ℂ F U) {z : Plane} (hz : z ∈ U) :
    Shape.divergence (holomorphicAreaField F) z = 2 * ‖deriv F z‖ ^ 2 := by
  have h1 := ((hF z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have h2 := (((hF.deriv hU) z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have h := h1.mul (Complex.conjCLE.hasFDerivAt.comp z h2)
  change Shape.divergence (F * (Complex.conjCLE ∘ deriv F)) z = _
  rw [Shape.divergence, h.fderiv, Complex.sq_norm, Complex.normSq_apply]
  change
    (F z * star ((1 : Plane) * deriv (deriv F) z) + star (deriv F z) * (1 * deriv F z)).re +
    (F z * star (Complex.I * deriv (deriv F) z) + star (deriv F z) * (Complex.I * deriv F z)).im = _
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- For a holomorphic map defined on a neighborhood of the closed disk, the
oriented area integral of its image circle equals twice its Dirichlet area. -/
theorem holomorphic_circle_cross_eq_disk_energy {U : Set Plane} (hU : IsOpen U)
    {F : Plane → Plane} (hF : DifferentiableOn ℂ F U) {r : ℝ} (hr : 0 < r)
    (hrU : Metric.closedBall (0 : Plane) r ⊆ U) :
    (∫ t in (-Real.pi)..Real.pi, planarCross (F (circleMap 0 r t))
      (deriv (fun s : ℝ => F (circleMap 0 r s)) t)) =
      2 * ∫ z in Metric.ball (0 : Plane) r, ‖deriv F z‖ ^ 2 := by
  let D : ConvexDomain := ⟨Metric.ball 0 r, Metric.isOpen_ball, Metric.isBounded_ball, convex_ball _ _,
    Metric.nonempty_ball.mpr hr⟩
  obtain ⟨η, hη, hone⟩ := exists_test_eq_one_near_compact hU (isCompact_closedBall 0 r) hrU
  obtain ⟨V, hV, hKV, hVone⟩ := mem_nhdsSet_iff_exists.mp hone
  let W := fun z => η z • holomorphicAreaField F z
  have hW : ContDiff ℝ 1 W := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ U
    · have hF1 : ContDiffAt ℝ 1 F z := ((hF.analyticOnNhd hU) z hz).contDiffAt.restrict_scalars ℝ
      have hF2 : ContDiffAt ℝ 1 (deriv F) z := (((hF.deriv hU).analyticOnNhd hU) z hz).contDiffAt.restrict_scalars ℝ
      exact (hη.1.of_le (by simp)).contDiffAt.smul (hF1.mul (Complex.conjCLE.contDiff.contDiffAt.comp z hF2))
    · have hnot : z ∉ tsupport η := fun h => hz (hη.2.2 h)
      apply (contDiffAt_const (c := (0 : Plane))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with x hx
      simp [W, hx]
  have hlocal (z : Plane) (hz : z ∈ Metric.closedBall 0 r) : W =ᶠ[𝓝 z] holomorphicAreaField F := by
    filter_upwards [hV.mem_nhds (hKV hz)] with x hx
    simp only [W, show η x = 1 from hVone hx, one_smul]
  have hrad : radialFrameCurve 0 (fun _ => r) = circleMap 0 r := by ext t : 1; simp [radialFrameCurve]
  have hgreen := smooth_radial_frame_divergence D 0 (fun _ => r) contDiff_const (fun _ => hr) rfl
    (fun _ _ s hs => by simp [D, Metric.mem_ball, norm_circleMap_zero, abs_of_pos hs]) hW
  rw [hrad] at hgreen
  have heq (t : ℝ) : planarCross (W (circleMap 0 r t)) (deriv (circleMap 0 r) t) =
      planarCross (F (circleMap 0 r t)) (deriv (fun s : ℝ => F (circleMap 0 r s)) t) := by
    let z := circleMap 0 r t
    have hz : z ∈ Metric.closedBall 0 r := by simp [z, Metric.mem_closedBall, abs_of_pos hr]
    have hd := ((hF z (hrU hz)).differentiableAt (hU.mem_nhds (hrU hz))).hasDerivAt
    have hc := (differentiable_circleMap 0 r t).hasDerivAt
    have hcomp := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hc
    rw [(hlocal z hz).eq_of_nhds, show deriv (fun s : ℝ => F (circleMap 0 r s)) t =
      deriv (circleMap 0 r) t * deriv F z from hcomp.deriv]
    simp [holomorphicAreaField, z, planarCross, Complex.mul_re, Complex.mul_im]
    ring
  simp_rw [heq] at hgreen
  rw [← hgreen, ← integral_const_mul]
  apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
  intro z hz
  have hzd := Metric.ball_subset_closedBall hz
  simpa only [Shape.divergence, (hlocal z hzd).fderiv_eq] using
    holomorphicAreaField_divergence hU hF (hrU hzd)

end Torsion

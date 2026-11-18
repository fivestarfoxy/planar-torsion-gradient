module

public import Torsion.Proof.PaperRadialGreen
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.MeasureTheory.Integral.CircleIntegral

@[expose] public section

/-! # Removing the simple zero from a holomorphic disk map -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory Metric
open scoped Topology

namespace Torsion

/-- A holomorphic function on a neighborhood of a closed disk has a smooth
angular trace on its boundary circle. -/
theorem holomorphic_circleTrace_contDiff {U : Set Plane} (hU : IsOpen U)
    {F : Plane → Plane} (hF : DifferentiableOn ℂ F U) {r : ℝ} (hr : 0 ≤ r)
    (hrU : closedBall (0 : Plane) r ⊆ U) :
    ContDiff ℝ 1 (fun t : ℝ => F (circleMap 0 r t)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have h : ContDiffAt ℝ 1 F (circleMap 0 r t) :=
    ((hF.analyticOnNhd hU _ (hrU (circleMap_mem_closedBall _ hr t))).contDiffAt).restrict_scalars ℝ
  exact h.comp t (contDiff_circleMap 0 r).contDiffAt

private theorem planarCross_angular_product (z g g' : Plane) :
    planarCross (z*g) ((z*Complex.I)*g + z*g') =
      ‖z*g‖^2 + ‖z‖^2 * planarCross g g' := by
  rw [norm_mul, mul_pow, Complex.sq_norm, Complex.sq_norm]
  simp only [planarCross, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- Factoring F(z)−F(0) = z G(z) gives a pointwise decomposition of the
oriented boundary area density into squared displacement and the area density of G. -/
theorem holomorphic_circle_cross_factor {U : Set Plane} (hU : IsOpen U)
    {F : Plane → Plane} (hF : DifferentiableOn ℂ F U) {r : ℝ} (hr : 0 < r)
    (hrU : closedBall (0 : Plane) r ⊆ U) (t : ℝ) :
    let c := circleMap (0 : Plane) r
    let G := dslope F 0
    planarCross (F (c t) - F 0) (deriv (fun s => F (c s) - F 0) t) =
      ‖F (c t) - F 0‖^2 + r^2 * planarCross (G (c t)) (deriv (fun s => G (c s)) t) := by
  let c := circleMap (0 : Plane) r
  let G := dslope F 0
  have he (s : ℝ) : F (c s) - F 0 = c s * G (c s) := by
    simpa only [G, sub_zero, smul_eq_mul] using (sub_smul_dslope F 0 (c s)).symm
  have hG : DifferentiableOn ℂ G U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds (hrU (mem_closedBall_self hr.le)))).2 hF
  have hGe := (holomorphic_circleTrace_contDiff hU hG hr.le hrU).differentiable one_ne_zero t
  have hd := ((hasDerivAt_circleMap 0 r t).mul hGe.hasDerivAt).deriv
  change planarCross (F (c t) - F 0) (deriv (fun s => F (c s) - F 0) t) =
    ‖F (c t) - F 0‖^2 + r^2 * planarCross (G (c t)) (deriv (fun s => G (c s)) t)
  rw [funext he, he t]
  have hd' : deriv (fun s => c s * G (c s)) t =
      (c t * Complex.I) * G (c t) + c t * deriv (fun s => G (c s)) t := by
    simpa only [c, Pi.mul_def, mul_comm, add_comm] using hd
  rw [hd', planarCross_angular_product, show ‖c t‖ = r from (norm_circleMap_zero r t).trans (abs_of_pos hr)]

end Torsion

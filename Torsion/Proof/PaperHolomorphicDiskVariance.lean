module

public import Torsion.Proof.PaperHolomorphicCircleFactor
public import Torsion.Proof.PaperHolomorphicDiskArea
public import Mathlib.MeasureTheory.Integral.CircleAverage

@[expose] public section

/-! # A holomorphic disk map's boundary displacement and Dirichlet integral -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory Metric

namespace Torsion

/-- The difference between twice the holomorphic area integral and the
squared boundary displacement is exactly the Dirichlet integral of the
holomorphic difference quotient, weighted by twice the squared radius. -/
theorem holomorphic_circle_variance_remainder {U : Set Plane} (hU : IsOpen U)
    {F : Plane → Plane} (hF : DifferentiableOn ℂ F U) {r : ℝ} (hr : 0 < r)
    (hrU : closedBall (0 : Plane) r ⊆ U) :
    (∫ t in (-Real.pi)..Real.pi, ‖F (circleMap 0 r t) - F 0‖^2) +
      2 * r^2 * (∫ z in ball (0 : Plane) r, ‖deriv (dslope F 0) z‖^2) =
      2 * ∫ z in ball (0 : Plane) r, ‖deriv F z‖^2 := by
  let c := circleMap (0 : Plane) r
  let H (z : Plane) := F z - F 0
  let G := dslope F 0
  have hH : DifferentiableOn ℂ H U := hF.sub_const _
  have hG : DifferentiableOn ℂ G U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds (hrU (mem_closedBall_self hr.le)))).2 hF
  have htrace := holomorphic_circleTrace_contDiff hU hG hr.le hrU
  have hcros : Continuous (fun t : ℝ => planarCross (G (c t)) (deriv (fun s => G (c s)) t)) :=
    continuous_planarCross htrace.continuous htrace.continuous_deriv_one
  have hdisp : Continuous (fun t : ℝ => ‖H (c t)‖^2) :=
    (holomorphic_circleTrace_contDiff hU hH hr.le hrU).continuous.norm.pow 2
  have hbase : (∫ t in (-Real.pi)..Real.pi, planarCross (H (c t)) (deriv (fun s => H (c s)) t)) =
      2 * ∫ z in ball (0 : Plane) r, ‖deriv F z‖^2 := by
    calc
      _ = 2 * ∫ z in ball (0 : Plane) r, ‖deriv H z‖^2 :=
        holomorphic_circle_cross_eq_disk_energy hU hH hr hrU
      _ = _ := by simp only [H, deriv_sub_const]
  have hfactor (t : ℝ) : planarCross (H (c t)) (deriv (fun s => H (c s)) t) =
      ‖H (c t)‖^2 + r^2 * planarCross (G (c t)) (deriv (fun s => G (c s)) t) :=
    holomorphic_circle_cross_factor hU hF hr hrU t
  simp_rw [hfactor] at hbase
  rw [intervalIntegral.integral_add (f := fun t => ‖H (c t)‖^2)
    (g := fun t => r^2 * planarCross (G (c t)) (deriv (fun s => G (c s)) t))
    (hdisp.intervalIntegrable _ _) ((continuous_const.mul hcros).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, holomorphic_circle_cross_eq_disk_energy hU hG hr hrU] at hbase
  change (∫ t in (-Real.pi)..Real.pi, ‖H (c t)‖^2) +
    2 * r^2 * (∫ z in ball (0 : Plane) r, ‖deriv G z‖^2) = _
  linarith only [hbase]

/-- The squared displacement of the holomorphic boundary trace relative to
the value at the center is bounded by twice its disk area integral. -/
theorem holomorphic_circle_variance_le_disk_energy {U : Set Plane} (hU : IsOpen U)
    {F : Plane → Plane} (hF : DifferentiableOn ℂ F U) {r : ℝ} (hr : 0 < r)
    (hrU : closedBall (0 : Plane) r ⊆ U) :
    (∫ t in (-Real.pi)..Real.pi, ‖F (circleMap 0 r t) - F 0‖^2) ≤
      2 * ∫ z in ball (0 : Plane) r, ‖deriv F z‖^2 := by
  rw [← holomorphic_circle_variance_remainder hU hF hr hrU]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity)
    (integral_nonneg (fun _ => sq_nonneg _)))

/-- With normalized angular measure, π times the boundary mean square
displacement is at most the Dirichlet integral on the disk. -/
theorem holomorphic_circleAverage_variance_le_disk_energy {U : Set Plane} (hU : IsOpen U)
    {F : Plane → Plane} (hF : DifferentiableOn ℂ F U) {r : ℝ} (hr : 0 < r)
    (hrU : closedBall (0 : Plane) r ⊆ U) :
    Real.pi * Real.circleAverage (fun z => ‖F z - F 0‖^2) 0 r ≤
      ∫ z in ball (0 : Plane) r, ‖deriv F z‖^2 := by
  let V (z : Plane) := ‖F z - F 0‖^2
  have hperiod := ((periodic_circleMap 0 r).comp V).intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at hperiod
  have h := holomorphic_circle_variance_le_disk_energy hU hF hr hrU
  change (∫ t in (-Real.pi)..Real.pi, V (circleMap 0 r t)) ≤ _ at h
  change (∫ t in (-Real.pi)..Real.pi, V (circleMap 0 r t)) = _ at hperiod
  rw [hperiod] at h
  simp only [Function.comp_apply] at h
  change Real.pi * Real.circleAverage V 0 r ≤ _
  rw [Real.circleAverage_def, smul_eq_mul, ← mul_assoc]
  rw [show Real.pi * (2 * Real.pi)⁻¹ = 1/2 by field_simp]
  linarith

/-- Boundary-only form of the disk estimate. The area density is signed and
the parameter increases counterclockwise. -/
theorem holomorphic_circle_variance_le_cross {U : Set Plane} (hU : IsOpen U)
    {F : Plane → Plane} (hF : DifferentiableOn ℂ F U) {r : ℝ} (hr : 0 < r)
    (hrU : closedBall (0 : Plane) r ⊆ U) :
    (∫ t in (-Real.pi)..Real.pi, ‖F (circleMap 0 r t) - F 0‖^2) ≤
      ∫ t in (-Real.pi)..Real.pi, planarCross (F (circleMap 0 r t))
        (deriv (fun s : ℝ => F (circleMap 0 r s)) t) := by
  rw [holomorphic_circle_cross_eq_disk_energy hU hF hr hrU]
  exact holomorphic_circle_variance_le_disk_energy hU hF hr hrU

end Torsion

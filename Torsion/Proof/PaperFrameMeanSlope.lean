module

public import Torsion.Proof.PaperArclengthReparam
public import Torsion.Proof.PaperRadialHermite
public import Torsion.Proof.PaperExamplesField
public import Torsion.Proof.PaperWeakFluxVolume
public import Mathlib.MeasureTheory.Integral.CircleIntegral

@[expose] public section

/-! # The disk maximizes the average inward torsion slope at fixed area -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

namespace Torsion

/-- The geometric perimeter is the integral of Euclidean boundary speed. -/
def radialFramePerimeter (c : Plane) (R : ℝ → ℝ) : ℝ :=
  ∫ t in (-Real.pi)..Real.pi, ‖deriv (radialFrameCurve c R) t‖

/-- The physical arclength average of the inward normal derivative. -/
def radialFrameMeanSlope (c : Plane) (R : ℝ → ℝ) (u : Plane → ℝ) : ℝ :=
  (∫ t in (-Real.pi)..Real.pi, frameInwardSlope u (radialFrameCurve c R t)
    (deriv (radialFrameCurve c R) t) * ‖deriv (radialFrameCurve c R) t‖) /
    radialFramePerimeter c R

/-- Green's area formula for the physical frame, including an arbitrary translation. -/
theorem radialFrame_signedArea (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ t, 0 < R t) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ t ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r t ∈ D.carrier ↔ r < R t)) :
    (∫ t in (-Real.pi)..Real.pi, planarCross (radialFrameCurve c R t)
      (deriv (radialFrameCurve c R) t)) = 2 * D.area := by
  have h := smooth_radial_frame_divergence D c R hR hpos hend hmem
    (W := id) contDiff_id
  simp only [id_eq] at h
  rw [← h]
  norm_num [Shape.divergence, ConvexDomain.area, Measure.real_def, mul_comm]

/-- The squared physical perimeter dominates 4π times the enclosed Euclidean area. -/
theorem smoothRadial_isoperimetric (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ t, 0 < R t) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ t ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r t ∈ D.carrier ↔ r < R t)) :
    4 * Real.pi * D.area ≤ (radialFramePerimeter c R)^2 := by
  have h := closedCurve_cross_le_length_sq_div_two_pi (neg_lt_self Real.pi_pos)
    (radialFrameCurve c R) (radialFrameCurve_contDiff c hR)
    (fun t _ => radialFrameCurve_speed_pos c hR hpos t) (radialFrameCurve_closed c hend)
  rw [radialFrame_signedArea D c R hR hpos hend hmem] at h
  change 2 * D.area ≤ (radialFramePerimeter c R)^2 / (2 * Real.pi) at h
  have h' := (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mp h
  linarith

/-- The circle of radius r has its actual geometric circumference 2πr. -/
theorem disk_radialFramePerimeter {r : ℝ} (hr : 0 < r) :
    radialFramePerimeter 0 (fun _ => r) = 2 * Real.pi * r := by
  have he : radialFrameCurve 0 (fun _ => r) = circleMap 0 r := by
    ext t : 1
    simp [radialFrameCurve]
  simp only [radialFramePerimeter, he, deriv_circleMap, norm_mul, Complex.norm_I, mul_one,
    norm_circleMap_zero, abs_of_pos hr, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- For the actual torsion solution of a disk, the average rim slope is r/2. -/
theorem disk_radialFrameMeanSlope {r : ℝ} (hr : 0 < r) :
    radialFrameMeanSlope 0 (fun _ => r) (PaperExamples.ellipseField r r) = r / 2 := by
  let D := PaperExamples.ellipseDomain hr hr
  have hD : D.carrier = Metric.ball (0 : Plane) r := PaperExamples.ellipse_eq_disk hr
  have hflux := smoothRadial_totalFlux D 0 (fun _ => r) contDiff_const (fun _ => hr) rfl
    (fun t _ s hs => by simp [hD, Metric.mem_ball, norm_circleMap_zero, abs_of_pos hs])
    (PaperExamples.ellipseField_contDiff r r)
    (fun z hz => by
      rw [hD, frontier_ball _ hr.ne'] at hz
      have hnorm : ‖z‖ = r := by simpa [Metric.mem_sphere] using hz
      rw [PaperExamples.disk_field hr, hnorm, sub_self, zero_div])
    (fun z _ => PaperExamples.ellipseField_laplacian hr hr z)
  rw [radialFrameMeanSlope, hflux, disk_radialFramePerimeter hr, PaperExamples.ellipse_area]
  field_simp

/-- The area-perimeter ratio is largest on the disk of the same area. -/
theorem smoothRadial_area_div_perimeter_le_diskSlope (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ t, 0 < R t) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ t ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r t ∈ D.carrier ↔ r < R t))
    {r : ℝ} (hr : 0 < r) (harea : Real.pi * r ^ 2 = D.area) :
    D.area / radialFramePerimeter c R ≤ radialFrameMeanSlope 0 (fun _ => r) (PaperExamples.ellipseField r r) := by
  let L := radialFramePerimeter c R
  have hL : 0 ≤ L := intervalIntegral.integral_nonneg (neg_le_self Real.pi_pos.le) (fun _ _ => norm_nonneg _)
  have hper := smoothRadial_isoperimetric D c R hR hpos hend hmem
  rw [← harea] at hper
  have hmin : 2 * Real.pi * r ≤ L := by
    apply (sq_le_sq₀ (by positivity) hL).mp
    dsimp [L]
    nlinarith only [hper]
  have hLpos : 0 < L := (show 0 < 2 * Real.pi * r by positivity).trans_le hmin
  rw [disk_radialFrameMeanSlope hr]
  apply (div_le_iff₀ hLpos).mpr
  nlinarith only [harea, mul_le_mul_of_nonneg_right hmin hr.le]

/-- Among all smooth frames with a given area the disk attains the largest
arclength-averaged inward slope. Its radius is determined by its area. -/
theorem smoothRadial_meanSlope_le_disk (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ t, 0 < R t) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ t ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r t ∈ D.carrier ↔ r < R t))
    {u : Plane → ℝ} (hu : ContDiff ℝ ∞ u) (hb : ∀ z ∈ frontier D.carrier, u z = 0)
    (hpoisson : ∀ z ∈ D.carrier, WeakHarmonicRegularity.planarLaplacian u z = -1)
    {r : ℝ} (hr : 0 < r) (harea : Real.pi * r ^ 2 = D.area) :
    radialFrameMeanSlope c R u ≤ radialFrameMeanSlope 0 (fun _ => r) (PaperExamples.ellipseField r r) := by
  rw [radialFrameMeanSlope, smoothRadial_totalFlux D c R hR hpos hend hmem hu hb hpoisson]
  exact smoothRadial_area_div_perimeter_le_diskSlope D c R hR hpos hend hmem hr harea

/-- Testing the actual weak inward flux against the constant boundary
value gives the same disk comparison without any smoothness premise on torsion. -/
theorem smoothRadial_weakMeanSlope_le_disk (T : DirichletTheory) (D : ConvexDomain)
    (c : Plane) (R : ℝ → ℝ) (hR : ContDiff ℝ 1 R) (hpos : ∀ t, 0 < R t)
    (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ t ∈ Ioo (-Real.pi) Real.pi, ∀ s : ℝ, 0 < s →
      (c + circleMap 0 s t ∈ D.carrier ↔ s < R t))
    {r : ℝ} (hr : 0 < r) (harea : Real.pi * r ^ 2 = D.area) :
    HermiteHadamard.weakBoundaryFlux D (T.solution D).weakGradient (fun _ => 1) /
      radialFramePerimeter c R ≤ radialFrameMeanSlope 0 (fun _ => r) (PaperExamples.ellipseField r r) := by
  have he : HermiteHadamard.weakBoundaryFlux D (T.solution D).weakGradient (fun _ => 1) = D.area := by
    simp [HermiteHadamard.weakBoundaryFlux, ConvexDomain.area, Measure.real_def]
  rw [he]
  exact smoothRadial_area_div_perimeter_le_diskSlope D c R hR hpos hend hmem hr harea

/-- The introductory area-one disk comparison in its exact numerical normalization. -/
theorem areaOne_meanSlope_le_disk (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ t, 0 < R t) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ t ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r t ∈ D.carrier ↔ r < R t))
    {u : Plane → ℝ} (hu : ContDiff ℝ ∞ u) (hb : ∀ z ∈ frontier D.carrier, u z = 0)
    (hpoisson : ∀ z ∈ D.carrier, WeakHarmonicRegularity.planarLaplacian u z = -1)
    (hA : D.area = 1) :
    radialFrameMeanSlope c R u ≤ 1 / (2 * Real.sqrt Real.pi) := by
  have hr : 0 < (Real.sqrt Real.pi)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr Real.pi_pos)
  have harea : Real.pi * ((Real.sqrt Real.pi)⁻¹)^2 = D.area := by
    rw [hA, inv_pow, Real.sq_sqrt Real.pi_pos.le, mul_inv_cancel₀ Real.pi_pos.ne']
  have h := smoothRadial_meanSlope_le_disk D c R hR hpos hend hmem hu hb hpoisson hr harea
  rw [disk_radialFrameMeanSlope hr] at h
  exact h.trans_eq (by ring)

end Torsion

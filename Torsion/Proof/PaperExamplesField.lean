module

public import Torsion.Proof.PaperExamples
public import Torsion.ClassicalWeakTorsion
public import Torsion.SignedBoundaryAdmission
public import Torsion.BoundaryLowerBound
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.Complex.Isometry

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Exact elliptical torsion fields

The quadratic solves the Dirichlet problem, and its boundary peak is the
essential supremum of the actual weak gradient on the open ellipse. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal ContDiff

namespace Torsion.PaperExamples

/-- Axis-aligned real-linear scaling of the complex plane. -/
def axes (a b : ℝ) : Plane →L[ℝ] Plane :=
  a • (Complex.ofRealCLM.comp Complex.reCLM) +
    b • Complex.imCLM.smulRight Complex.I

@[simp] theorem axes_re (a b : ℝ) (z : Plane) : (axes a b z).re = a * z.re := by
  simp [axes, Complex.real_smul, Complex.mul_re]

@[simp] theorem axes_im (a b : ℝ) (z : Plane) : (axes a b z).im = b * z.im := by
  simp [axes, Complex.real_smul, Complex.mul_im]

/-- The open ellipse as the image of the open unit disk. -/
def ellipse (A B : ℝ) : Set Plane := axes A B '' Metric.ball 0 1

theorem mem_ellipse_iff {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {z : Plane} :
    z ∈ ellipse A B ↔ (z.re / A) ^ 2 + (z.im / B) ^ 2 < 1 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [axes_re, axes_im, mul_div_cancel_left₀ _ hA.ne', mul_div_cancel_left₀ _ hB.ne']
    have hn : ‖w‖ < 1 := by simpa using hw
    nlinarith [Complex.sq_norm_sub_sq_re w, norm_nonneg w]
  · intro h
    refine ⟨⟨z.re / A, z.im / B⟩, ?_, ?_⟩
    · simp only [Metric.mem_ball, dist_zero_right]
      have he := Complex.sq_norm_sub_sq_re (⟨z.re / A, z.im / B⟩ : ℂ)
      dsimp at he
      nlinarith
    · apply Complex.ext <;> simp <;> field_simp

theorem ellipse_isOpen {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : IsOpen (ellipse A B) := by
  rw [show ellipse A B = {z : Plane | (z.re / A) ^ 2 + (z.im / B) ^ 2 < 1} from
    Set.ext fun _ => mem_ellipse_iff hA hB]
  exact isOpen_lt (by fun_prop) continuous_const

theorem ellipse_bounded (A B : ℝ) : Bornology.IsBounded (ellipse A B) := by
  exact (axes A B).lipschitzWith.isBounded_image Metric.isBounded_ball

def ellipseDomain {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : ConvexDomain where
  carrier := ellipse A B
  isOpen := ellipse_isOpen hA hB
  bounded := ellipse_bounded A B
  convex := (convex_ball (0 : Plane) 1).linear_image (axes A B).toLinearMap
  nonempty := (Metric.nonempty_ball.mpr (by norm_num : (0 : ℝ) < 1)).image _

private theorem axes_det (A B : ℝ) : (axes A B).toLinearMap.det = A * B := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

theorem ellipse_area {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (ellipseDomain hA hB).area = Real.pi * A * B := by
  change (volume ((axes A B) '' Metric.ball (0 : Plane) 1)).toReal = _
  rw [Measure.addHaar_image_continuousLinearMap, axes_det, abs_of_pos (mul_pos hA hB)]
  simp [Complex.volume_ball, hA.le, hB.le]
  ring

def ellipseField (A B : ℝ) (z : Plane) : ℝ :=
  A ^ 2 * B ^ 2 / (2 * (A ^ 2 + B ^ 2)) -
  (B ^ 2 / (A ^ 2 + B ^ 2)) * z.re ^ 2 / 2 -
  (A ^ 2 / (A ^ 2 + B ^ 2)) * z.im ^ 2 / 2

theorem ellipseField_formula {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (z : Plane) :
    ellipseField A B z = A ^ 2 * B ^ 2 / (2 * (A ^ 2 + B ^ 2)) *
      (1 - (z.re / A) ^ 2 - (z.im / B) ^ 2) := by
  unfold ellipseField
  field_simp

theorem ellipseField_pos_iff {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (z : Plane) :
    0 < ellipseField A B z ↔ z ∈ ellipse A B := by
  rw [ellipseField_formula hA hB, mem_ellipse_iff hA hB,
    mul_pos_iff_of_pos_left (by positivity)]
  constructor <;> intro h <;> linarith

theorem ellipseField_contDiff (A B : ℝ) : ContDiff ℝ ∞ (ellipseField A B) := by
  unfold ellipseField
  exact (contDiff_const.sub ((contDiff_const.mul (Complex.reCLM.contDiff.pow 2)).div_const 2)).sub
    ((contDiff_const.mul (Complex.imCLM.contDiff.pow 2)).div_const 2)

/-- The genuine classical gradient of the quadratic, on the full plane. -/
def ellipseGradient (A B : ℝ) : Plane →L[ℝ] Plane :=
  axes (-(B ^ 2 / (A ^ 2 + B ^ 2))) (-(A ^ 2 / (A ^ 2 + B ^ 2)))

theorem ellipseField_hasGradientAt (A B : ℝ) (z : Plane) :
    HasGradientAt (ellipseField A B) (ellipseGradient A B z) z := by
  have hr := Complex.reCLM.hasFDerivAt (x := z)
  have hi := Complex.imCLM.hasFDerivAt (x := z)
  have hd := ((hasFDerivAt_const (A ^ 2 * B ^ 2 / (2 * (A ^ 2 + B ^ 2))) z).sub
    (((hr.pow 2).const_mul (B ^ 2 / (A ^ 2 + B ^ 2))).mul_const (2⁻¹ : ℝ))).sub
    (((hi.pow 2).const_mul (A ^ 2 / (A ^ 2 + B ^ 2))).mul_const (2⁻¹ : ℝ))
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hd using 1
  ext v
  simp [ellipseGradient, InnerProductSpace.toDual_apply_apply, Complex.inner, Complex.mul_re]
  ring

theorem ellipseField_laplacian {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (z : Plane) :
    WeakHarmonicRegularity.planarLaplacian (ellipseField A B) z = -1 := by
  have he := funext (fun w => (ellipseField_hasGradientAt A B w).gradient)
  unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
  rw [he, (ellipseGradient A B).hasFDerivAt.fderiv]
  simp [ellipseGradient]
  field_simp
  ring

/-- The interior slope bound is sharp at each short-axis endpoint. -/
theorem ellipseGradient_le {A B : ℝ} (hB : 0 < B) (hBA : B ≤ A) {z : Plane}
    (hz : z ∈ ellipse A B) : ‖ellipseGradient A B z‖ ≤ shortAxisSlope A B := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hn : ‖w‖ < 1 := by simpa using hw
  have hw₂ : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
    nlinarith [Complex.sq_norm_sub_sq_re w, norm_nonneg w]
  have hA := lt_of_lt_of_le hB hBA
  have hs : 0 < A^2 + B^2 := by positivity
  have hg := Complex.sq_norm_sub_sq_re (ellipseGradient A B (axes A B w))
  simp only [ellipseGradient, axes_re, axes_im] at hg
  have hc : B^2 ≤ A^2 := by nlinarith
  have hsum : (B^2 / A^2) * w.re^2 + w.im^2 ≤ 1 := by
    have hratio := (div_le_one (sq_pos_of_pos hA)).2 hc
    nlinarith [mul_le_mul_of_nonneg_right hratio (sq_nonneg w.re)]
  have hsq : ‖ellipseGradient A B (axes A B w)‖ ^ 2 ≤ (shortAxisSlope A B) ^ 2 := by
    unfold shortAxisSlope ellipseGradient
    rw [sub_eq_iff_eq_add.mp hg]
    field_simp at hsum ⊢
    nlinarith [mul_nonneg (show 0 ≤ A^2 - (B^2 * w.re^2 + w.im^2 * A^2) by linarith)
      (show 0 ≤ A^2 * B^2 by positivity)]
  have hslope : 0 ≤ shortAxisSlope A B := by unfold shortAxisSlope; positivity
  nlinarith [norm_nonneg (ellipseGradient A B (axes A B w))]

theorem ellipseGradient_tip {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ‖ellipseGradient A B (axes A B Complex.I)‖ = shortAxisSlope A B := by
  have he : ellipseGradient A B (axes A B Complex.I) =
      (-(shortAxisSlope A B) : ℝ) • Complex.I := by
    apply Complex.ext <;> simp only [ellipseGradient, axes_re, axes_im, Complex.smul_re, Complex.smul_im, Complex.I_re,
      Complex.I_im, smul_eq_mul, shortAxisSlope] <;> ring
  have hs : 0 ≤ shortAxisSlope A B := by unfold shortAxisSlope; positivity
  simp [he, abs_of_nonneg hs]

/-- The slope deficit separates distance from the boundary and from the
minor axis. This identifies every maximizing point on a genuine ellipse. -/
private theorem ellipse_gradient_deficit {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (w : Plane) :
    shortAxisSlope A B ^ 2 - ‖ellipseGradient A B (axes A B w)‖ ^ 2 =
      (A ^ 2 * B ^ 2 / (A ^ 2 + B ^ 2) ^ 2) *
      ((A ^ 2 - B ^ 2) * w.re ^ 2 + A ^ 2 * (1 - ‖w‖ ^ 2)) := by
  rw [sub_eq_iff_eq_add.mp (Complex.sq_norm_sub_sq_re (ellipseGradient A B (axes A B w))),
    sub_eq_iff_eq_add.mp (Complex.sq_norm_sub_sq_re w)]
  simp only [shortAxisSlope, ellipseGradient, axes_re, axes_im]
  field_simp
  ring

theorem ellipseGradient_eq_peak_iff {A B : ℝ} (hB : 0 < B) (hBA : B < A)
    {w : Plane} (hw : ‖w‖ ≤ 1) :
    ‖ellipseGradient A B (axes A B w)‖ = shortAxisSlope A B ↔
      w = Complex.I ∨ w = -Complex.I := by
  have hA := hB.trans hBA
  constructor
  · intro he
    have hc : 0 < A ^ 2 * B ^ 2 / (A ^ 2 + B ^ 2) ^ 2 := by positivity
    have hc' : 0 < A ^ 2 - B ^ 2 := by nlinarith
    have hgap := ellipse_gradient_deficit hA hB w
    rw [he, sub_self] at hgap
    have hz := (mul_eq_zero.mp hgap.symm).resolve_left hc.ne'
    have h₁ := mul_nonneg hc'.le (sq_nonneg w.re)
    have hnorm : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have h₂ := mul_nonneg (sq_nonneg A) hnorm
    have he₁ : (A ^ 2 - B ^ 2) * w.re ^ 2 = 0 := by linarith
    have he₂ : A ^ 2 * (1 - ‖w‖ ^ 2) = 0 := by linarith
    have hre := (mul_eq_zero.mp he₁).resolve_left hc'.ne'
    have hn := (mul_eq_zero.mp he₂).resolve_left (sq_pos_of_pos hA).ne'
    have hr : w.re = 0 := by nlinarith
    have hi : w.im = 1 ∨ w.im = -1 := by
      have hm : (w.im - 1) * (w.im + 1) = 0 := by
        nlinarith [Complex.sq_norm_sub_sq_re w]
      rcases mul_eq_zero.mp hm with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hi with h | h
    · exact Or.inl (Complex.ext (by simpa using hr) (by simpa using h))
    · exact Or.inr (Complex.ext (by simpa using hr) (by simpa using h))
  · rintro (rfl | rfl) <;> simpa using ellipseGradient_tip hA hB

/-- Equal semiaxes give the Euclidean disk, in the same complex coordinates
and with the same radius as the comparison frame in the paper. -/
theorem ellipse_eq_disk {R : ℝ} (hR : 0 < R) :
    ellipse R R = Metric.ball (0 : Plane) R := by
  ext z
  rw [mem_ellipse_iff hR hR, Metric.mem_ball, dist_zero_right]
  have h := Complex.sq_norm_sub_sq_re z
  constructor
  · intro hz
    field_simp at hz
    nlinarith [norm_nonneg z]
  · intro hz
    field_simp
    nlinarith [norm_nonneg z]

theorem disk_field {R : ℝ} (hR : 0 < R) (z : Plane) :
    ellipseField R R z = (R ^ 2 - ‖z‖ ^ 2) / 4 := by
  unfold ellipseField
  rw [sub_eq_iff_eq_add.mp (Complex.sq_norm_sub_sq_re z)]
  field_simp
  ring

/-- On the disk the normal slope is constant on the entire rim. -/
theorem disk_rim_slope {R : ℝ} (hR : 0 < R) {z : Plane} (hz : ‖z‖ = R) :
    ‖ellipseGradient R R z‖ = R / 2 := by
  have he : ellipseGradient R R z = (- (1 / 2 : ℝ)) • z := by
    apply Complex.ext <;> simp only [ellipseGradient, axes_re, axes_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> field_simp <;> ring
  rw [he, norm_smul, hz]
  norm_num
  ring

/-- Opposite endpoints of the short axis have the same peak slope. -/
theorem ellipseGradient_opposite_tip {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ‖ellipseGradient A B (axes A B (-Complex.I))‖ = shortAxisSlope A B := by
  simpa using ellipseGradient_tip hA hB

/-- The ellipse has its greatest deflection at its center. -/
theorem ellipseField_le_center {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (z : Plane) :
    ellipseField A B z ≤ ellipseField A B 0 := by
  simp only [ellipseField, Complex.zero_re, Complex.zero_im, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_div, sub_zero]
  have h₁ : 0 ≤ (B ^ 2 / (A ^ 2 + B ^ 2)) * z.re ^ 2 / 2 := by positivity
  have h₂ : 0 ≤ (A ^ 2 / (A ^ 2 + B ^ 2)) * z.im ^ 2 / 2 := by positivity
  linarith

/-- At area one the disk has greater central deflection than any unequal
ellipse. Equality forces equal axes. -/
theorem unit_area_ellipse_center_le_disk {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (harea : Real.pi * A * B = 1) :
    ellipseField A B 0 ≤ 1 / (4 * Real.pi) ∧
      (ellipseField A B 0 = 1 / (4 * Real.pi) ↔ A = B) := by
  simp only [ellipseField, Complex.zero_re, Complex.zero_im, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_div, sub_zero]
  have hs : 0 < 2 * (A^2 + B^2) := by positivity
  have hp : 0 < 4 * Real.pi := by positivity
  rw [div_le_div_iff₀ hs hp, div_eq_div_iff hs.ne' hp.ne']
  have h := congrArg (fun t : ℝ => 4 * A * B * t) harea
  constructor
  · nlinarith [sq_nonneg (A-B)]
  · constructor
    · intro he
      nlinarith [sq_nonneg (A-B)]
    · rintro rfl
      nlinarith

end Torsion.PaperExamples

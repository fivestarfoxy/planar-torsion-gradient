module

public import Torsion.Definitions
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Tactic

@[expose] public section

/-! # A centered holomorphic chart of the upper half-plane

The Möbius coordinate sends zero to any prescribed point in the upper
half-plane. Its inverse is explicit and maps the entire half-plane into
the open unit disk. -/

noncomputable section
open Set
open scoped Topology
namespace Torsion.Spectral

/-- A disk coordinate centered at `a`, with the omitted boundary point at 1. -/
def centeredDiskChart (a z : Plane) : Plane := (a - star a * z) / (1 - z)

/-- The inverse Möbius coordinate. -/
def centeredDiskChartInverse (a w : Plane) : Plane := (w - a) / (w - star a)

@[simp] theorem centeredDiskChart_zero (a : Plane) : centeredDiskChart a 0 = a := by
  simp [centeredDiskChart]

private theorem disk_denom_ne {z : Plane} (hz : z ∈ Metric.ball 0 1) : 1 - z ≠ 0 := by
  apply sub_ne_zero.mpr
  rintro rfl
  simp at hz

private theorem halfPlane_denom_ne {a w : Plane} (ha : a ∈ upperHalfPlane)
    (hw : w ∈ upperHalfPlane) : w - star a ≠ 0 := by
  intro h
  have hi := congrArg Complex.im (sub_eq_zero.mp h)
  have hwa : 0 < w.im := hw
  have haa : 0 < a.im := ha
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

theorem centeredDiskChart_mapsTo {a : Plane} (ha : a ∈ upperHalfPlane) :
    MapsTo (centeredDiskChart a) (Metric.ball 0 1) upperHalfPlane := by
  intro z hz
  have hnorm : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  have hp : 0 < 1 - Complex.normSq z := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  have him : (centeredDiskChart a z).im = a.im * (1 - Complex.normSq z) / Complex.normSq (1-z) := by
    simp only [centeredDiskChart, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
    rw [← sub_div]
    congr 1
    simp only [Complex.normSq_apply]
    ring
  change 0 < (centeredDiskChart a z).im
  rw [him]
  exact div_pos (mul_pos (show 0 < a.im from ha) hp) (Complex.normSq_pos.mpr (disk_denom_ne hz))

theorem centeredDiskChartInverse_mapsTo {a : Plane} (ha : a ∈ upperHalfPlane) :
    MapsTo (centeredDiskChartInverse a) upperHalfPlane (Metric.ball 0 1) := by
  intro w hw
  have hdiff : ‖w - a‖ ^ 2 < ‖w - star a‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [mul_pos (show 0 < w.im from hw) (show 0 < a.im from ha)]
  rw [Metric.mem_ball, dist_zero_right, centeredDiskChartInverse, norm_div,
    div_lt_one (norm_pos_iff.mpr (halfPlane_denom_ne ha hw))]
  nlinarith [norm_nonneg (w-a), norm_nonneg (w-star a)]

theorem centeredDiskChartInverse_chart {a z : Plane} (ha : a ∈ upperHalfPlane)
    (hz : z ∈ Metric.ball 0 1) : centeredDiskChartInverse a (centeredDiskChart a z) = z := by
  apply (div_eq_iff (halfPlane_denom_ne ha (centeredDiskChart_mapsTo ha hz))).mpr
  unfold centeredDiskChart
  field_simp [disk_denom_ne hz]
  ring

theorem centeredDiskChart_chartInverse {a w : Plane} (ha : a ∈ upperHalfPlane)
    (hw : w ∈ upperHalfPlane) : centeredDiskChart a (centeredDiskChartInverse a w) = w := by
  apply (div_eq_iff (disk_denom_ne (centeredDiskChartInverse_mapsTo ha hw))).mpr
  have h : centeredDiskChartInverse a w * (w - star a) = w - a :=
    div_mul_cancel₀ _ (halfPlane_denom_ne ha hw)
  linear_combination h

theorem centeredDiskChart_analyticOnNhd (a : Plane) :
    AnalyticOnNhd ℂ (centeredDiskChart a) (Metric.ball 0 1) := by
  intro z hz
  exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) (disk_denom_ne hz)

theorem centeredDiskChartInverse_analyticOnNhd {a : Plane} (ha : a ∈ upperHalfPlane) :
    AnalyticOnNhd ℂ (centeredDiskChartInverse a) upperHalfPlane := by
  intro w hw
  exact (analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
    (halfPlane_denom_ne ha hw)

/-- The derivative of the centered chart is explicit at every point of the open disk. -/
theorem centeredDiskChart_hasDerivAt (a : Plane) {z : Plane} (hz : z ∈ Metric.ball 0 1) :
    HasDerivAt (centeredDiskChart a) ((a - star a) / (1-z)^2) z := by
  convert ((hasDerivAt_const z a).sub ((hasDerivAt_const z (star a)).mul (hasDerivAt_id z))).div
    ((hasDerivAt_const z 1).sub (hasDerivAt_id z)) (disk_denom_ne hz) using 1
  · rfl
  · simp [Pi.mul_def]
    ring

theorem centeredDiskChart_deriv_ne_zero {a z : Plane} (ha : a ∈ upperHalfPlane)
    (hz : z ∈ Metric.ball 0 1) : deriv (centeredDiskChart a) z ≠ 0 := by
  rw [(centeredDiskChart_hasDerivAt a hz).deriv]
  exact div_ne_zero (halfPlane_denom_ne ha ha) (pow_ne_zero _ (disk_denom_ne hz))

theorem centeredDiskChart_injOn {a : Plane} (ha : a ∈ upperHalfPlane) :
    InjOn (centeredDiskChart a) (Metric.ball 0 1) := by
  intro z hz w hw he
  rw [← centeredDiskChartInverse_chart ha hz, he, centeredDiskChartInverse_chart ha hw]

theorem centeredDiskChart_image {a : Plane} (ha : a ∈ upperHalfPlane) :
    centeredDiskChart a '' Metric.ball 0 1 = upperHalfPlane := by
  refine (centeredDiskChart_mapsTo ha).image_subset.antisymm ?_
  intro w hw
  exact ⟨_, centeredDiskChartInverse_mapsTo ha hw, centeredDiskChart_chartInverse ha hw⟩

/-- The explicit Möbius map and inverse form a homeomorphism on the open sets. -/
def centeredDiskHomeomorph (a : Plane) (ha : a ∈ upperHalfPlane) :
    Metric.ball (0 : Plane) 1 ≃ₜ upperHalfPlane where
  toFun z := ⟨centeredDiskChart a z, centeredDiskChart_mapsTo ha z.property⟩
  invFun w := ⟨centeredDiskChartInverse a w, centeredDiskChartInverse_mapsTo ha w.property⟩
  left_inv z := Subtype.ext (centeredDiskChartInverse_chart ha z.property)
  right_inv w := Subtype.ext (centeredDiskChart_chartInverse ha w.property)
  continuous_toFun := (centeredDiskChart_analyticOnNhd a).continuousOn.domRestrict.subtype_mk _
  continuous_invFun := (centeredDiskChartInverse_analyticOnNhd ha).continuousOn.domRestrict.subtype_mk _

@[simp] theorem centeredDiskHomeomorph_apply (a : Plane) (ha : a ∈ upperHalfPlane)
    (z : Metric.ball (0 : Plane) 1) :
    ((centeredDiskHomeomorph a ha z : upperHalfPlane) : Plane) = centeredDiskChart a z := rfl

end Torsion.Spectral

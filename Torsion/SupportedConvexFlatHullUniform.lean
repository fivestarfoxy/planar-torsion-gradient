import Torsion.SupportedConvexFlatHull

/-! # A uniform quantitative flat patch for actual convex outer hulls -/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Torsion

/-- A patch radius depending only on the added segment, a lower interior
height and an upper distance bound for the chosen interior point. -/
def flatHullPatchRadius (r h M : ℝ) : ℝ :=
  min (h / 2) (r / (4 * (1 + M / h)))

theorem flatHullPatchRadius_pos {r h M : ℝ} (hr : 0 < r) (hh : 0 < h) (hM : 0 ≤ M) :
    0 < flatHullPatchRadius r h M := by
  dsimp [flatHullPatchRadius]
  exact lt_min (half_pos hh) (div_pos hr (by positivity))

/-- One explicit half-ball lies in the actual flat hull uniformly whenever
its interior point has a fixed lower height and upper norm bound. -/
theorem halfBall_subset_flatOuterHull_of_point_bounds {D : Set Plane} (hD : IsOpen D)
    {a : Plane} (ha : a ∈ D) {r h M : ℝ} (hr : 0 < r) (hh : 0 < h)
    (hM : 0 ≤ M) (hheight : h ≤ a.im) (hnorm : ‖a‖ ≤ M) :
    upperHalfPlane ∩ ball (0 : Plane) (flatHullPatchRadius r h M) ⊆ flatOuterHull D r := by
  have haim : 0 < a.im := hh.trans_le hheight
  let K : ℝ := 1 + M / h
  have hK : 0 < K := by dsimp [K]; positivity
  intro z hz
  have hzpos : 0 < z.im := hz.1
  have hzρ : ‖z‖ < flatHullPatchRadius r h M := by
    simpa only [mem_ball, dist_zero_right] using hz.2
  have hzhalf : ‖z‖ < h / 2 := hzρ.trans_le (min_le_left _ _)
  have hzrad : ‖z‖ < r / (4 * K) := hzρ.trans_le (min_le_right _ _)
  let t : ℝ := z.im / a.im
  let s : ℝ := (z.re - t * a.re) / (1 - t)
  have ht : 0 < t := div_pos hzpos haim
  have hta : t * a.im = z.im := div_mul_cancel₀ _ haim.ne'
  have hth : t * h ≤ ‖z‖ := by
    calc
      t * h ≤ t * a.im := mul_le_mul_of_nonneg_left hheight ht.le
      _ = z.im := hta
      _ ≤ ‖z‖ := Complex.im_le_norm z
  have hthalf : t < 1 / 2 := by nlinarith
  have htone : t < 1 := by linarith
  have htupper : t ≤ ‖z‖ / h := (le_div_iff₀ hh).mpr hth
  have hare : |a.re| ≤ M := (Complex.abs_re_le_norm a).trans hnorm
  have hnum : |z.re - t * a.re| ≤ ‖z‖ * K := by
    calc
      |z.re - t * a.re| ≤ |z.re| + |t * a.re| := abs_sub _ _
      _ = |z.re| + t * |a.re| := by rw [abs_mul, abs_of_pos ht]
      _ ≤ ‖z‖ + (‖z‖ / h) * M :=
        add_le_add (Complex.abs_re_le_norm z) (mul_le_mul htupper hare (abs_nonneg _) (div_nonneg (norm_nonneg _) hh.le))
      _ = ‖z‖ * K := by dsimp [K]; ring
  have hsmall : ‖z‖ * K < r / 4 := by
    have hh' := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hK)).mp hzrad
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    convert hh' using 1 <;> ring
  have hden : 0 < 1 - t := sub_pos.mpr htone
  have hs : |s| < r := by
    dsimp [s]
    rw [abs_div, abs_of_pos hden]
    apply (div_lt_iff₀ hden).mpr
    have hn := hnum.trans_lt hsmall
    nlinarith
  have haHull : a ∈ interior (convexHull ℝ (closure D ∪ horizontalBase r)) :=
    subset_flatOuterHull hD r ha
  have hsHull : (s : Plane) ∈ convexHull ℝ (closure D ∪ horizontalBase r) := by
    apply subset_convexHull ℝ _
    right
    exact ⟨by simpa only [mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs] using hs.le, by simp⟩
  have hcombo := (convex_convexHull ℝ (closure D ∪ horizontalBase r)).combo_interior_self_mem_interior
    haHull hsHull ht (sub_nonneg.mpr htone.le) (add_sub_cancel _ _)
  have heq : t • a + (1 - t) • (s : Plane) = z := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      dsimp [s]
      field_simp [hden.ne']
    · simp only [Complex.add_im, Complex.smul_im, Complex.ofReal_im, mul_zero, add_zero]
      simpa only [smul_eq_mul, mul_zero, add_zero] using hta
  simpa only [heq] using hcombo

/-- The same quantitative patch is the exact marked flat half-ball whenever
the original domain is supported in the upper half-plane. -/
theorem flatOuterHull_inter_ball_of_point_bounds {D : Set Plane} (hD : IsOpen D)
    (hhalf : D ⊆ upperHalfPlane) {a : Plane} (ha : a ∈ D)
    {r h M : ℝ} (hr : 0 < r) (hh : 0 < h) (hM : 0 ≤ M)
    (hheight : h ≤ a.im) (hnorm : ‖a‖ ≤ M) :
    flatOuterHull D r ∩ ball (0 : Plane) (flatHullPatchRadius r h M) =
      upperHalfPlane ∩ ball (0 : Plane) (flatHullPatchRadius r h M) := by
  apply Subset.antisymm
  · exact inter_subset_inter_left _ (flatOuterHull_subset_upper hhalf r)
  · intro z hz
    exact ⟨halfBall_subset_flatOuterHull_of_point_bounds hD ha hr hh hM hheight hnorm hz, hz.2⟩

end Torsion

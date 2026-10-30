import Torsion.Definitions
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Concrete flat outer hulls at a supported boundary point

Adjoining a short real segment and taking the interior of its convex hull
produces an actual marked domain. It contains the original supported domain
and remains within twice the segment radius of it. The flat neighborhood
comes from convex combinations with a fixed actual interior point.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Torsion

/-- The closed horizontal segment of radius `r`, in Euclidean coordinates. -/
def horizontalBase (r : ℝ) : Set Plane := closedBall 0 r ∩ {z | z.im = 0}

/-- An actual outer convex hull, with its added segment on the support line. -/
def flatOuterHull (D : Set Plane) (r : ℝ) : Set Plane :=
  interior (convexHull ℝ (closure D ∪ horizontalBase r))

theorem subset_flatOuterHull {D : Set Plane} (hD : IsOpen D) (r : ℝ) :
    D ⊆ flatOuterHull D r :=
  interior_maximal (fun _ hz => subset_convexHull ℝ _ (Or.inl (subset_closure hz))) hD

theorem flatOuterHull_convex (D : Set Plane) (r : ℝ) : Convex ℝ (flatOuterHull D r) :=
  (convex_convexHull ℝ _).interior

theorem flatOuterHull_bounded {D : Set Plane} (hD : Bornology.IsBounded D) (r : ℝ) :
    Bornology.IsBounded (flatOuterHull D r) :=
  (isBounded_convexHull.mpr
    (hD.closure.union (isBounded_closedBall.subset inter_subset_left))).subset interior_subset

/-- No point below or on the support line enters the open hull. -/
theorem flatOuterHull_subset_upper {D : Set Plane} (hD : D ⊆ upperHalfPlane) (r : ℝ) :
    flatOuterHull D r ⊆ upperHalfPlane := by
  have hcl : closure D ⊆ {z : Plane | 0 ≤ z.im} := by
    exact (isClosed_le continuous_const Complex.continuous_im).closure_subset_iff.mpr
      (fun z hz => (show 0 < z.im from hD hz).le)
  have hbase : horizontalBase r ⊆ {z : Plane | 0 ≤ z.im} := by
    intro z hz
    exact hz.2.ge
  have hh := convexHull_min (union_subset hcl hbase) (convex_halfSpace_im_ge 0)
  simpa only [flatOuterHull, Complex.interior_setOf_le_im, upperHalfPlane] using interior_mono hh

/-- The added base is quantitatively small in the actual ambient metric. -/
theorem flatOuterHull_subset_thickening {D : Set Plane} (hc : Convex ℝ D)
    (hzero : (0 : Plane) ∈ closure D) {r : ℝ} (hr : 0 < r) :
    flatOuterHull D r ⊆ thickening (2 * r) D := by
  apply interior_subset.trans
  apply convexHull_min _ (hc.thickening _)
  apply union_subset
  · exact closure_subset_thickening (by positivity) D
  · intro z hz
    rw [← thickening_closure]
    apply mem_thickening_iff.mpr
    exact ⟨0, hzero, (mem_closedBall.mp hz.1).trans_lt (by linarith)⟩

/-- An actual positive half-ball lies in the hull, without any boundary
smoothness hypothesis on the original domain. -/
theorem exists_halfBall_subset_flatOuterHull {D : Set Plane} (hD : IsOpen D)
    (hDU : D ⊆ upperHalfPlane) (hne : D.Nonempty) {r : ℝ} (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ upperHalfPlane ∩ ball (0 : Plane) ρ ⊆ flatOuterHull D r := by
  obtain ⟨a, ha⟩ := hne
  have haim : 0 < a.im := hDU ha
  let t : Plane → ℝ := fun z => z.im / a.im
  let s : Plane → ℝ := fun z => (z.re - t z * a.re) / (1 - t z)
  have ht0 : t 0 = 0 := by simp [t]
  have hs0 : s 0 = 0 := by simp [s, ht0]
  have ht : ContinuousAt t (0 : Plane) := Complex.continuous_im.continuousAt.div_const _
  have hs : ContinuousAt s (0 : Plane) := by
    exact (Complex.continuous_re.continuousAt.sub (ht.mul_const _)).div
      (continuousAt_const.sub ht) (by simp [ht0])
  have hn : ∀ᶠ z : Plane in 𝓝 0, t z < 1 ∧ |s z| < r := by
    have hnt : ∀ᶠ z : Plane in 𝓝 0, t z < 1 :=
      ht.eventually (gt_mem_nhds (by simp [ht0]))
    have hns : ∀ᶠ z : Plane in 𝓝 0, |s z| < r :=
      hs.abs.eventually (gt_mem_nhds (by simpa [hs0] using hr))
    exact hnt.and hns
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ρ, hρ, ?_⟩
  intro z hz
  have htz : 0 < t z := div_pos hz.1 haim
  have htz1 : t z < 1 := (hball hz.2).1
  have hsz : |s z| < r := (hball hz.2).2
  have haHull : a ∈ interior (convexHull ℝ (closure D ∪ horizontalBase r)) :=
    subset_flatOuterHull hD r ha
  have hsHull : (s z : Plane) ∈ convexHull ℝ (closure D ∪ horizontalBase r) := by
    apply subset_convexHull ℝ _
    right
    exact ⟨by simpa only [mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs] using hsz.le, by simp⟩
  have hcombo := (convex_convexHull ℝ (closure D ∪ horizontalBase r)).combo_interior_self_mem_interior
    haHull hsHull htz (sub_nonneg.mpr htz1.le) (add_sub_cancel _ _)
  have heq : t z • a + (1 - t z) • (s z : Plane) = z := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      dsimp [s]
      field_simp [ne_of_gt (sub_pos.mpr htz1)]
    · simp only [Complex.add_im, Complex.smul_im, Complex.ofReal_im, mul_zero, add_zero]
      dsimp [t]
      simpa only [mul_zero, add_zero] using div_mul_cancel₀ z.im haim.ne'
  simpa only [heq] using hcombo

/-- The construction is genuinely marked, with a proved common flat patch. -/
theorem flatOuterHull_isMarked {D : Set Plane} (hD : IsOpen D)
    (hb : Bornology.IsBounded D) (hDU : D ⊆ upperHalfPlane) (hne : D.Nonempty)
    {r : ℝ} (hr : 0 < r) : IsMarked (flatOuterHull D r) := by
  obtain ⟨ρ, hρ, hhalf⟩ := exists_halfBall_subset_flatOuterHull hD hDU hne hr
  refine ⟨isOpen_interior, flatOuterHull_bounded hb r, flatOuterHull_subset_upper hDU r,
    ρ, hρ, ?_⟩
  apply Subset.antisymm
  · exact inter_subset_inter_left _ (flatOuterHull_subset_upper hDU r)
  · intro z hz
    exact ⟨hhalf hz, hz.2⟩

/-- Every supported convex domain has actual marked convex outer domains
with arbitrarily small metric error. -/
theorem ConvexDomain.exists_marked_flat_outer (D : ConvexDomain)
    (hDU : D.carrier ⊆ upperHalfPlane) (hzero : (0 : Plane) ∈ closure D.carrier)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ E : ConvexDomain, IsMarked E.carrier ∧ D.carrier ⊆ E.carrier ∧
      E.carrier ⊆ thickening ε D.carrier := by
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  let E : ConvexDomain := ⟨flatOuterHull D.carrier r, isOpen_interior,
    flatOuterHull_bounded D.bounded r, flatOuterHull_convex _ _,
    D.nonempty.mono (subset_flatOuterHull D.isOpen r)⟩
  refine ⟨E, flatOuterHull_isMarked D.isOpen D.bounded hDU D.nonempty hr,
    subset_flatOuterHull D.isOpen r, ?_⟩
  simpa only [r, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    flatOuterHull_subset_thickening D.convex hzero hr

end Torsion

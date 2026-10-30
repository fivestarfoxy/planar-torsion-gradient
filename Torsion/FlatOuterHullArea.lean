module

public import Torsion.SupportedConvexFlatHull
public import Torsion.ConvexOuterApproximation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative area cost of the actual flat outer hull

An actual interior ball controls the metric thickening by a homothety
about its center. The hull construction is therefore bounded by the exact
quadratic Euclidean area factor, uniformly over all supporting frames.
-/

noncomputable section
open Set Metric MeasureTheory
open scoped Pointwise

namespace Torsion.ConvexDomain

/-- The concrete flat hull as a member of the original admissible class. -/
def flatHull (D : ConvexDomain) (r : ℝ) : ConvexDomain where
  carrier := flatOuterHull D.carrier r
  isOpen := isOpen_interior
  bounded := flatOuterHull_bounded D.bounded r
  convex := flatOuterHull_convex _ _
  nonempty := D.nonempty.mono (subset_flatOuterHull D.isOpen r)

@[simp] theorem flatHull_carrier (D : ConvexDomain) (r : ℝ) :
    (D.flatHull r).carrier = flatOuterHull D.carrier r := rfl

/-- Exact quadratic area loss, without any supporting-half-plane premise. -/
theorem flatHull_area_le (D : ConvexDomain) {a : Plane} {h r : ℝ}
    (hh : 0 < h) (hball : ball a h ⊆ D.carrier)
    (hzero : (0 : Plane) ∈ closure D.carrier) (hr : 0 < r) :
    (D.flatHull r).area ≤ (1 + 2 * r / h)^2 * D.area := by
  let Dc := D.translate (-a)
  let Ec := (D.flatHull r).translate (-a)
  have hballc : ball (0 : Plane) h ⊆ Dc.carrier := by
    intro z hz
    change z - (-a) ∈ D.carrier
    rw [sub_neg_eq_add]
    apply hball
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  have houter : Ec.carrier ⊆ thickening (2*r) Dc.carrier := by
    intro z hz
    have hzE : z + a ∈ (D.flatHull r).carrier := by
      simpa only [Ec, mem_translate, sub_neg_eq_add] using hz
    obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.mp
      (flatOuterHull_subset_thickening D.convex hzero hr hzE)
    apply mem_thickening_iff.mpr
    refine ⟨y-a, ?_, ?_⟩
    · simpa only [Dc, mem_translate, sub_neg_eq_add, sub_add_cancel] using hy
    · calc
        dist z (y-a) = dist (z+a) ((y-a)+a) := (dist_add_right _ _ _).symm
        _ = dist (z+a) y := by rw [sub_add_cancel]
        _ < 2*r := hzy
  have hs : 0 < 1 + 2*r/h := by positivity
  have hcontain := houter.trans (thickening_subset_dilate_of_convex Dc.convex hh
    (show 0 < 2*r by positivity) hballc)
  have harea := ENNReal.toReal_mono
    ((Dc.dilate (1+2*r/h) hs).bounded.measure_lt_top (μ := (volume : Measure Plane))).ne
    (measure_mono (μ := (volume : Measure Plane)) hcontain)
  change Ec.area ≤ (Dc.dilate (1+2*r/h) hs).area at harea
  simpa only [Ec, Dc, translate_area, dilate_area] using harea

/-- The area normalization loses at most the actual linear dilation factor. -/
theorem flatHull_sqrt_area_le (D : ConvexDomain) {a : Plane} {h r : ℝ}
    (hh : 0 < h) (hball : ball a h ⊆ D.carrier)
    (hzero : (0 : Plane) ∈ closure D.carrier) (hr : 0 < r) :
    Real.sqrt (D.flatHull r).area ≤ (1+2*r/h)*Real.sqrt D.area := by
  calc
    _ ≤ Real.sqrt ((1+2*r/h)^2*D.area) :=
      Real.sqrt_le_sqrt (D.flatHull_area_le hh hball hzero hr)
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

end Torsion.ConvexDomain

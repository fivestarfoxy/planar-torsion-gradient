module

public import Torsion.SupportedConvexFlatHull

@[expose] public section

/-! # Marking a point in the interior of a straight side -/

noncomputable section
open Set Metric

namespace Torsion

/-- If the horizontal base already belongs to the boundary of a convex
domain, its supporting flat hull is the original open domain. -/
theorem ConvexDomain.flatOuterHull_eq_of_horizontalBase_subset_frontier
    (D : ConvexDomain) {r : ℝ} (hbase : horizontalBase r ⊆ frontier D.carrier) :
    flatOuterHull D.carrier r = D.carrier := by
  have hsub : horizontalBase r ⊆ closure D.carrier := hbase.trans frontier_subset_closure
  rw [flatOuterHull, union_eq_self_of_subset_right hsub, D.convex.closure.convexHull_eq,
    D.convex.interior_closure_eq_interior_of_nonempty_interior
      (by simpa only [D.isOpen.interior_eq] using D.nonempty), D.isOpen.interior_eq]

/-- Lemma 6.1. A straight boundary segment of positive length with the
origin in its middle supplies a genuine marked half-ball. -/
theorem ConvexDomain.isMarked_of_horizontalBase_subset_frontier (D : ConvexDomain)
    (hhalf : D.carrier ⊆ upperHalfPlane) {r : ℝ} (hr : 0 < r)
    (hbase : horizontalBase r ⊆ frontier D.carrier) : IsMarked D.carrier := by
  have h := flatOuterHull_isMarked D.isOpen D.bounded hhalf D.nonempty hr
  rwa [D.flatOuterHull_eq_of_horizontalBase_subset_frontier hbase] at h

end Torsion

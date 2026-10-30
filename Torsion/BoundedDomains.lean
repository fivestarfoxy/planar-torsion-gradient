import Torsion.Poincare
import Mathlib.Analysis.Normed.Module.Convex

/-! # Poincaré estimates on arbitrary bounded domains

No convexity, openness or boundary regularity is required for the graph
closure estimate. Enclose the set in a ball and use the proved planar
Poincaré inequality there. This includes the slit domains in Section 3.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Torsion

theorem IsTest.mono {D E : Set Plane} {f : Plane → ℝ}
    (hf : IsTest D f) (hDE : D ⊆ E) : IsTest E f :=
  ⟨hf.1, hf.2.1, hf.2.2.trans hDE⟩

theorem MemH10.mono {D E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) (hDE : D ⊆ E) : MemH10 E u g := by
  rcases hu with ⟨hu, hg, f, hf, hfu, hfg⟩
  exact ⟨hu, hg, f, fun n => (hf n).mono hDE, hfu, hfg⟩

/-- Every bounded planar set lies in a nonempty bounded open convex domain. -/
theorem exists_containing_convexDomain {D : Set Plane} (hD : Bornology.IsBounded D) :
    ∃ B : ConvexDomain, D ⊆ B.carrier := by
  obtain ⟨r, hr, hsub⟩ := hD.subset_ball_lt 0 (0 : Plane)
  exact ⟨⟨Metric.ball 0 r, Metric.isOpen_ball, Metric.isBounded_ball,
    convex_ball (0 : Plane) r, Metric.nonempty_ball.mpr hr⟩, hsub⟩

/-- A positive finite Poincaré constant for the actual H¹₀ closure of every
bounded set, including nonconvex and empty domains. -/
theorem exists_poincare_constant_of_bounded {D : Set Plane} (hD : Bornology.IsBounded D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (u : Plane → ℝ) (g : Plane → Plane),
      MemH10 D u g → eLpNorm u 2 volume ≤ ENNReal.ofReal K * eLpNorm g 2 volume := by
  obtain ⟨B, hDB⟩ := exists_containing_convexDomain hD
  obtain ⟨K, hK, hp⟩ := exists_poincare_constant B
  exact ⟨K, hK, fun u g h => hp u g (h.mono hDB)⟩

end Torsion
end

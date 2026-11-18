module

public import Torsion.Proof.PaperBoundaryFrameComparison

@[expose] public section

/-! # The maximum normal quotient on every bounded open convex domain -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Torsion

/-- Lemma 5.1 of the manuscript. For the original convex domain there is a
single boundary point and a fixed entering inward unit supporting normal at
which the actual torsion quotient tends to the entire weak-gradient norm. -/
theorem DirichletTheory.exists_maximizing_normal_quotient (T : DirichletTheory)
    (D : ConvexDomain) :
    ∃ (U : Plane → ℝ) (p n : Plane), Continuous U ∧
      IsWeakTorsion D.carrier U (T.solution D).weakGradient ∧
      (∀ x ∉ D.carrier, U x = 0) ∧ ((T.solution D).value =ᵐ[volume.restrict D.carrier] U) ∧
      p ∈ frontier D.carrier ∧ ‖n‖ = 1 ∧
      (∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) n (z - p)) ∧
      (∀ᶠ t : ℝ in 𝓝[>] 0, p + t • n ∈ D.carrier) ∧
      Tendsto (fun t : ℝ => U (p + t • n) / t) (𝓝[>] 0) (𝓝 (T.G D).toReal) := by
  obtain ⟨s⟩ := T.exists_maximizingNormalSequence D
  exact ⟨s.value, s.point, s.normal, s.continuous, s.weak, s.zero_off, s.value_eq,
    s.point_mem, s.unit, s.support, s.fixed_normal_enters s.rectangleComparison,
    s.fixed_normal_quotient s.rectangleComparison⟩

end Torsion

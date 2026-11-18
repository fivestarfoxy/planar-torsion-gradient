module

public import Torsion.NormalFrame
public import Torsion.WeakTorsionRepresentative

@[expose] public section

/-! # Pulling a continuous torsion representative into a physical supporting frame -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ContDiff

namespace Torsion

/-- A continuous zero extension agrees everywhere with the interior-smooth
Dirichlet representative. This identifies its classical gradient on the
open set, including after a change of physical coordinates. -/
theorem IsWeakTorsion.continuous_zero_extension_interior_data {D : ConvexDomain}
    {U : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D.carrier U g)
    (hc : Continuous U) (hz : ∀ x ∉ D.carrier, U x = 0) :
    ContDiffOn ℝ ∞ U D.carrier ∧ g =ᵐ[volume.restrict D.carrier] gradient U := by
  obtain ⟨V, hV, hVz, hUV, hgV⟩ := hu.exists_smooth_representative D.isOpen D.bounded
  have hEq := Measure.eqOn_open_of_ae_eq hUV D.isOpen hc.continuousOn hV.continuousOn
  have heq : U = V := by
    funext x
    by_cases hx : x ∈ D.carrier
    · exact hEq hx
    · rw [hz x hx, hVz x hx]
  rw [heq]
  exact ⟨hV, hgV⟩

/-- Rigid pullback preserves the global Lipschitz constant, including
across the boundary of the zero extension. -/
theorem lipschitzWith_inNormalFrame {U : Plane → ℝ} {L : ℝ≥0} (h : LipschitzWith L U)
    (p n : Plane) (hn : ‖n‖ = 1) :
    LipschitzWith L (fun z => U (normalFrame n hn z + p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_add_right, LinearIsometryEquiv.dist_map] using
    h.dist_le_mul (normalFrame n hn x + p) (normalFrame n hn y + p)

/-- The real coordinate points along the oriented tangent and the imaginary
coordinate points along the given unit inward normal. -/
theorem normalFrame_coordinates (n : Plane) (hn : ‖n‖ = 1) (z : Plane) :
    normalFrame n hn z = z.im • n + z.re • (-Complex.I * n) := by
  let e := normalFrame n hn
  have hid : z = z.re • (1 : Plane) + z.im • Complex.I := by
    simp [Complex.real_smul]
  have h1 : e (1 : Plane) = -Complex.I * n := by
    change (-Complex.I * n) * 1 = _
    exact mul_one _
  calc
    e z = e (z.re • (1 : Plane) + z.im • Complex.I) := congrArg e hid
    _ = _ := by rw [map_add, map_smul, map_smul, h1, show e Complex.I = n from normalFrame_I n hn, add_comm]

end Torsion

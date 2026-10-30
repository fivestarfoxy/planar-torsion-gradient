module

public import Torsion.ShapeDeformation
public import Torsion.RadialGeometry
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A concrete smooth radial collar

A single scalar bump is one on the complete range of a positive continuous
reference radius, and zero near radius zero and outside a finite annulus.
No regularity of the reference radius beyond continuity is needed here.
-/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace Torsion.Shape

def radialCollar (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M) :
    ContDiffBump ((m + M) / 2 : ℝ) where
  rIn := M / 2 - m / 4
  rOut := M / 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

theorem radialCollar_eq_one {m M r : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (hr : r ∈ Icc m M) : radialCollar m M hm hmM r = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [mem_closedBall, Real.dist_eq]
  change |r - (m + M) / 2| ≤ M / 2 - m / 4
  exact abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩

theorem radialCollar_support {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    tsupport (radialCollar m M hm hmM : ℝ → ℝ) ⊆ Icc (m / 2) (M + m / 2) := by
  rw [ContDiffBump.tsupport_eq]
  intro r hr
  rw [mem_closedBall, Real.dist_eq] at hr
  change |r - (m + M) / 2| ≤ M / 2 at hr
  rcases abs_le.mp hr with ⟨hr₁, hr₂⟩
  exact ⟨by linarith, by linarith⟩

theorem radialCollar_zero {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    radialCollar m M hm hmM 0 = 0 := by
  by_contra hne
  have h := radialCollar_support hm hmM (subset_tsupport _ hne)
  linarith [h.1]

theorem radialCollar_hasCompactSupport {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    HasCompactSupport (radialCollar m M hm hmM : ℝ → ℝ) :=
  ContDiffBump.hasCompactSupport _

/-- A positive continuous reference profile supplies an actual smooth
compact scalar collar equal to one at every reference outer radius. -/
theorem exists_radialCollar {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc 0 Real.pi))
    (hpos : ∀ θ ∈ Icc 0 Real.pi, 0 < R θ) :
    ∃ (β : ℝ → ℝ) (m M : ℝ), ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      0 < m ∧ m ≤ M ∧ tsupport β ⊆ Icc (m / 2) (M + m / 2) ∧
      β 0 = 0 ∧ (∀ θ ∈ Icc 0 Real.pi, β (R θ) = 1) := by
  have hnonempty : (Icc (0 : ℝ) Real.pi).Nonempty := ⟨0, le_rfl, Real.pi_pos.le⟩
  obtain ⟨θmin, hθmin, hmin⟩ := isCompact_Icc.exists_isMinOn hnonempty hR
  obtain ⟨θmax, hθmax, hmax⟩ := isCompact_Icc.exists_isMaxOn hnonempty hR
  let m := R θmin
  let M := R θmax
  have hm : 0 < m := hpos θmin hθmin
  have hmM : m ≤ M := hmax hθmin
  refine ⟨radialCollar m M hm hmM, m, M, ContDiffBump.contDiff _,
    radialCollar_hasCompactSupport hm hmM, hm, hmM,
    radialCollar_support hm hmM, radialCollar_zero hm hmM, ?_⟩
  intro θ hθ
  exact radialCollar_eq_one hm hmM ⟨hmin hθ, hmax hθ⟩

/-- Smooth compact scalar functions have a finite global Lipschitz bound. -/
theorem exists_lipschitz_scalar_of_contDiff_compact {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β) :
    ∃ K : ℝ≥0, LipschitzWith K β := by
  obtain ⟨C, hC⟩ := (hβc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hβ.continuous_fderiv (by simp))
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  refine ⟨K, lipschitzWith_of_nnnorm_fderiv_le (hβ.differentiable (by simp)) ?_⟩
  intro x
  change ‖fderiv ℝ β x‖ ≤ max C 0
  exact (hC x).trans (le_max_left _ _)

end Torsion.Shape

module

public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Smooth uniform approximation with support inside a prescribed open set

This uses the pinned mathlib convolution approximation. Its local error
estimate also preserves zero neighborhoods, so the approximants retain
compact support inside the original prescribed open set.
-/

noncomputable section
open Set Metric
open scoped Topology ContDiff

namespace Torsion

/-- A continuous compactly supported real function admits arbitrarily close
uniform smooth approximants with compact support in any prescribed open
neighborhood of its support. -/
theorem exists_smooth_compact_approximation {f : ℝ → ℝ} {U : Set ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hU : IsOpen U)
    (hfs : tsupport f ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ∀ x, dist (g x) (f x) < ε := by
  obtain ⟨δU, hδU, hδsub⟩ := hfc.exists_cthickening_subset_open hU hfs
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (hfc.uniformContinuous_of_continuous hf) (ε / 2) (half_pos hε)
  let η := min δU δ
  have hη : 0 < η := lt_min hδU hδ
  obtain ⟨g, hg, happrox⟩ := hf.exists_contDiff_dist_le_of_forall_mem_ball_dist_le hη
  have hzero : ∀ x, x ∉ cthickening η (tsupport f) → g x = 0 := by
    intro x hx
    have hfx : f x = 0 := by
      by_contra hne
      exact hx (self_subset_cthickening (tsupport f) (subset_tsupport f hne))
    have hball : ∀ y ∈ ball x η, dist (f y) (f x) ≤ 0 := by
      intro y hy
      have hfy : f y = 0 := by
        by_contra hne
        apply hx
        exact mem_cthickening_of_dist_le x y η (tsupport f) (subset_tsupport f hne)
          (by simpa only [dist_comm] using (mem_ball.mp hy).le)
      simp [hfx, hfy]
    have hdist := happrox x 0 hball
    have hEq : g x = f x := dist_le_zero.mp hdist
    exact hEq.trans hfx
  have hsupp : tsupport g ⊆ cthickening η (tsupport f) := by
    apply closure_minimal _ isClosed_cthickening
    intro x hx
    by_contra hnot
    exact hx (hzero x hnot)
  refine ⟨g, hg, hfc.cthickening.of_isClosed_subset (isClosed_tsupport g) hsupp,
    hsupp.trans ((cthickening_mono (min_le_left δU δ) _).trans hδsub), ?_⟩
  intro x
  apply (happrox x (ε / 2) ?_).trans_lt (half_lt_self hε)
  intro y hy
  apply (hmod ?_).le
  exact (mem_ball.mp hy).trans_le (min_le_right δU δ)

/-- The difference of two continuous angular profiles agreeing on endpoint
neighborhoods extends to a genuine continuous compactly supported function
on the real line, with support strictly inside the open angular interval. -/
theorem exists_compact_endpoint_difference {R₀ S : ℝ → ℝ}
    (h₀ : ContinuousOn R₀ (Icc 0 Real.pi))
    (hS : ContinuousOn S (Icc 0 Real.pi))
    (hnear : ∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ Icc 0 Real.pi,
      (θ ≤ ε ∨ Real.pi - ε ≤ θ) → S θ = R₀ θ) :
    ∃ f : ℝ → ℝ, Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo 0 Real.pi ∧
      ∀ θ ∈ Icc 0 Real.pi, f θ = S θ - R₀ θ := by
  obtain ⟨ε, hε, hnear⟩ := hnear
  let η := min ε (Real.pi / 4)
  have hη : 0 < η := lt_min hε (by positivity)
  have hηε : η ≤ ε := min_le_left _ _
  have hηπ : η < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  let d : Icc (0 : ℝ) Real.pi → ℝ := fun θ => S θ - R₀ θ
  let f : ℝ → ℝ := IccExtend Real.pi_pos.le d
  have hc : Continuous f := continuous_IccExtend_iff.mpr (hS.sub h₀).restrict
  have hzero : ∀ x, x ≤ η ∨ Real.pi - η ≤ x → f x = 0 := by
    intro x hx
    let q := projIcc (0 : ℝ) Real.pi Real.pi_pos.le x
    have hq : (q : ℝ) ≤ ε ∨ Real.pi - ε ≤ (q : ℝ) := by
      rcases hx with hx | hx
      · left
        apply le_trans _ hηε
        change max 0 (min Real.pi x) ≤ η
        exact max_le hη.le ((min_le_right _ _).trans hx)
      · right
        have hlow : Real.pi - η ≤ (q : ℝ) := by
          change Real.pi - η ≤ max 0 (min Real.pi x)
          exact (le_min (by linarith) hx).trans (le_max_right _ _)
        linarith
    exact sub_eq_zero.mpr (hnear q q.property hq)
  have hsupport : tsupport f ⊆ Icc η (Real.pi - η) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    constructor
    · apply le_of_not_gt
      intro h
      exact hx (hzero x (Or.inl h.le))
    · apply le_of_not_gt
      intro h
      exact hx (hzero x (Or.inr h.le))
  refine ⟨f, hc, isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hsupport,
    hsupport.trans (fun x hx => ⟨hη.trans_le hx.1, hx.2.trans_lt (by linarith)⟩), ?_⟩
  intro θ hθ
  exact IccExtend_of_mem Real.pi_pos.le d hθ

/-- Smooth compact approximants for the difference of endpoint-preserving
continuous profiles, uniformly on the entire closed angular interval. -/
theorem exists_smooth_compact_endpoint_approximation {R₀ S : ℝ → ℝ}
    (h₀ : ContinuousOn R₀ (Icc 0 Real.pi))
    (hS : ContinuousOn S (Icc 0 Real.pi))
    (hnear : ∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ Icc 0 Real.pi,
      (θ ≤ ε ∨ Real.pi - ε ≤ θ) → S θ = R₀ θ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ioo 0 Real.pi ∧
      ∀ θ ∈ Icc 0 Real.pi, dist (g θ) (S θ - R₀ θ) < δ := by
  obtain ⟨f, hf, hfc, hfs, hfeq⟩ := exists_compact_endpoint_difference h₀ hS hnear
  obtain ⟨g, hg, hgc, hgs, happrox⟩ :=
    exists_smooth_compact_approximation hf hfc isOpen_Ioo hfs hδ
  exact ⟨g, hg, hgc, hgs, fun θ hθ => hfeq θ hθ ▸ happrox θ⟩

end Torsion

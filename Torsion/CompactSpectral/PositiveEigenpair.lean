module

/-
The weak compact maximum argument is adapted from Adam Benenson's
`compact-spectral`, commit 72cd62dbdd4c397d26fc0c5777d60fea2211e938.
Copyright (c) 2026 Adam Benenson. Released under the Apache 2.0 license;
see the accompanying LICENSE file. The explicit positive maximum and
nonzero-eigenvalue conclusions extend that argument.
-/
public import Torsion.CompactSpectral.RayleighCompact

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Positive extremal eigenpairs of compact self-adjoint operators

The compactness and Rayleigh-calculus proofs are supplied by the attributed
Lean 4.19 backport in `RayleighCompact`. Here the positive maximum is selected
explicitly, and a nonzero operator yields a nonzero eigenvalue. No spectral
existence hypothesis is hidden in the statements.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Torsion.CompactSelfAdjoint
open Torsion.CompactSpectral

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A positive value of the actual quadratic form forces a positive largest
Rayleigh eigenvalue, attained by a unit vector. -/
theorem exists_positive_max_eigenpair_of_positive_quadratic
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    (hTc : IsCompactOperator (T : E → E))
    (hpositive : ∃ x : E, 0 < T.reApplyInnerSelf x) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ v : E, ‖v‖ = 1 ∧
      T v = (μ : 𝕜) • v ∧ ∀ y : E, T.rayleighQuotient y ≤ μ := by
  classical
  obtain ⟨x, hx⟩ := hpositive
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0, ContinuousLinearMap.reApplyInnerSelf_apply] at hx
  let s : Set (WeakSpace 𝕜 E) := weakClosedBall (𝕜 := 𝕜) (E := E) 1
  let f : WeakSpace 𝕜 E → ℝ := fun z => T.reApplyInnerSelf (z : E)
  have hs : IsCompact s := isCompact_weakClosedBall 1
  have hsne : s.Nonempty := by
    refine ⟨0, ?_⟩
    change (0 : E) ∈ closedBall (0 : E) 1
    exact Metric.mem_closedBall_self zero_le_one
  have hfc : ContinuousOn f s :=
    continuousOn_weakClosedBall_reApplyInnerSelf_of_isCompactOperator T hTc 1
  obtain ⟨xMax, hxMax, hmax⟩ := hs.exists_isMaxOn hsne hfc
  let c : 𝕜 := ((‖x‖⁻¹ : ℝ) : 𝕜)
  let y : E := c • x
  have hc : c ≠ 0 := by simp [c, hx0]
  have hynorm : ‖y‖ = 1 := by simp [y, c, norm_smul, hx0]
  have hymem : (y : WeakSpace 𝕜 E) ∈ s := by
    change y ∈ closedBall (0 : E) 1
    exact mem_closedBall_zero_iff.2 hynorm.le
  have hypos : 0 < f (y : WeakSpace 𝕜 E) := by
    change 0 < T.reApplyInnerSelf (c • x)
    rw [ContinuousLinearMap.reApplyInnerSelf_smul]
    exact mul_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hc)) hx
  have hmaxpos : 0 < f xMax := lt_of_lt_of_le hypos (hmax hymem)
  have hxMaxnorm : ‖(xMax : E)‖ = 1 :=
    extremizer_mem_unit_sphere
      (fun c z => by
        change T.reApplyInnerSelf (c • (z : E)) = ‖c‖ ^ 2 * T.reApplyInnerSelf (z : E)
        exact ContinuousLinearMap.reApplyInnerSelf_smul T (z : E))
      hxMax (σ := 1) (by simpa using hmaxpos)
      (fun z hz => by simpa using hmax hz)
  have hmaxsphere : IsMaxOn T.reApplyInnerSelf (sphere (0 : E) ‖(xMax : E)‖) (xMax : E) := by
    intro z hz
    have hz' : z ∈ closedBall (0 : E) 1 := by
      rw [hxMaxnorm] at hz
      exact sphere_subset_closedBall hz
    exact hmax hz'
  let μ : ℝ := T.rayleighQuotient (xMax : E)
  have hμ : 0 < μ := by
    simpa [μ, ContinuousLinearMap.rayleighQuotient, hxMaxnorm, f] using hmaxpos
  have heigen : T (xMax : E) = (μ : 𝕜) • (xMax : E) :=
    hT.eq_smul_self_of_isLocalExtrOn (Or.inr hmaxsphere.localize)
  refine ⟨μ, hμ, (xMax : E), hxMaxnorm, heigen, ?_⟩
  intro z
  by_cases hz : z = 0
  · simpa [hz, ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using hμ.le
  let d : 𝕜 := ((‖z‖⁻¹ : ℝ) : 𝕜)
  have hd : d ≠ 0 := by simp [d, hz]
  have hdnorm : ‖d • z‖ = 1 := by simp [d, norm_smul, hz]
  have hdmem : d • z ∈ sphere (0 : E) ‖(xMax : E)‖ := by
    simp only [mem_sphere_zero_iff_norm, hxMaxnorm, hdnorm]
  calc
    T.rayleighQuotient z = T.rayleighQuotient (d • z) := (T.rayleigh_smul z hd).symm
    _ = T.reApplyInnerSelf (d • z) := by simp [ContinuousLinearMap.rayleighQuotient, hdnorm]
    _ ≤ T.reApplyInnerSelf (xMax : E) := hmaxsphere hdmem
    _ = μ := by simp [μ, ContinuousLinearMap.rayleighQuotient, hxMaxnorm]

/-- Every nonzero nonnegative compact self-adjoint operator has a positive
largest Rayleigh eigenvalue, with an actual unit eigenvector. -/
theorem exists_positive_max_eigenpair
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    (hTc : IsCompactOperator (T : E → E)) (hT0 : T ≠ 0)
    (hnonneg : ∀ x : E, 0 ≤ T.reApplyInnerSelf x) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ v : E, ‖v‖ = 1 ∧
      T v = (μ : 𝕜) • v ∧ ∀ y : E, T.rayleighQuotient y ≤ μ := by
  obtain ⟨x, hx⟩ := exists_reApplyInnerSelf_ne_zero_of_isSelfAdjoint T hT hT0
  exact exists_positive_max_eigenpair_of_positive_quadratic T hT hTc
    ⟨x, lt_of_le_of_ne (hnonneg x) (Ne.symm hx)⟩

/-- A nonzero compact self-adjoint operator has a nonzero real eigenvalue
and a unit eigenvector. This excludes the zero eigenspace alternative. -/
theorem exists_nonzero_eigenpair
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    (hTc : IsCompactOperator (T : E → E)) (hT0 : T ≠ 0) :
    ∃ μ : ℝ, μ ≠ 0 ∧ ∃ v : E, ‖v‖ = 1 ∧ T v = (μ : 𝕜) • v := by
  obtain ⟨x, hx⟩ := exists_reApplyInnerSelf_ne_zero_of_isSelfAdjoint T hT hT0
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hnegpos : 0 < (-T).reApplyInnerSelf x := by
      simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using neg_pos.mpr hxneg
    obtain ⟨μ, hμ, v, hv, heigen, _⟩ :=
      exists_positive_max_eigenpair_of_positive_quadratic (-T) hT.neg hTc.neg ⟨x, hnegpos⟩
    refine ⟨-μ, neg_ne_zero.mpr hμ.ne', v, hv, ?_⟩
    simpa using congrArg (fun z : E => -z) heigen
  · obtain ⟨μ, hμ, v, hv, heigen, _⟩ :=
      exists_positive_max_eigenpair_of_positive_quadratic T hT hTc ⟨x, hxpos⟩
    exact ⟨μ, hμ.ne', v, hv, heigen⟩

end Torsion.CompactSelfAdjoint

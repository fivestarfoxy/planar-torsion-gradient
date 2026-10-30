module

public import Torsion.CompactSpectral.TwoEigenpairs

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Second variational selection after a specified first eigenvector

The invariant-complement construction applies to any specified
maximal first eigenvector. This permits proved ground-state choices to be
used while retaining the second vector's actual variational property.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Torsion.CompactSelfAdjoint

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A specified maximal first eigenvector admits a genuine
second positive variational eigenvector in its orthogonal complement. -/
theorem exists_positive_second_after_first
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    (hTc : IsCompactOperator (T : E → E))
    (hnonneg : ∀ x : E, 0 ≤ T.reApplyInnerSelf x)
    (hTwo : ∀ v : E, ∃ f : E, inner (𝕜 := 𝕜) f v = 0 ∧ T f ≠ 0)
    {μ₁ : ℝ} {v₁ : E}
    (he₁ : T v₁ = (μ₁ : 𝕜) • v₁)
    (hfirst : ∀ z : E, T.reApplyInnerSelf z ≤ μ₁ * ‖z‖ ^ 2) :
    ∃ μ₂ : ℝ, 0 < μ₂ ∧ μ₂ ≤ μ₁ ∧ ∃ v₂ : E,
      ‖v₂‖ = 1 ∧ inner (𝕜 := 𝕜) v₁ v₂ = 0 ∧ T v₂ = (μ₂ : 𝕜) • v₂ ∧
        (∀ z : E, inner (𝕜 := 𝕜) v₁ z = 0 → T.reApplyInnerSelf z ≤ μ₂ * ‖z‖ ^ 2) := by
  classical
  let V : Submodule 𝕜 E := (Submodule.span 𝕜 ({v₁} : Set E))ᗮ
  have hV : ∀ w ∈ V, T w ∈ V := by
    intro w hw
    change w ∈ (𝕜 ∙ v₁)ᗮ at hw
    change T w ∈ (𝕜 ∙ v₁)ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hw ⊢
    calc
      inner (𝕜 := 𝕜) v₁ (T w) = inner (𝕜 := 𝕜) (T v₁) w := (hT.isSymmetric v₁ w).symm
      _ = 0 := by rw [he₁, inner_smul_left, hw, mul_zero]
  let Ulin : V →ₗ[𝕜] V := (T : E →ₗ[𝕜] E).restrict hV
  have hUcLin : IsCompactOperator (Ulin : V → V) := hTc.restrict' hV
  let U : V →L[𝕜] V := ContinuousLinearMap.mkOfIsCompactOperator hUcLin
  have hUc : IsCompactOperator (U : V → V) := hUcLin
  have hUs : IsSelfAdjoint U := by
    apply LinearMap.IsSymmetric.isSelfAdjoint
    exact hT.isSymmetric.restrict_invariant hV
  obtain ⟨f, hfv₁, hTf⟩ := hTwo v₁
  have hfV : f ∈ V := by
    change f ∈ (𝕜 ∙ v₁)ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact inner_eq_zero_symm.mp hfv₁
  let fV : V := ⟨f, hfV⟩
  have hU0 : U ≠ 0 := by
    intro hU0
    have h := congrArg (fun z : V => (z : E)) (show U fV = 0 by simp [hU0])
    exact hTf h
  have hUnonneg : ∀ z : V, 0 ≤ U.reApplyInnerSelf z := by
    intro z
    exact hnonneg (z : E)
  obtain ⟨μ₂, hμ₂, v₂, hv₂, he₂, hb₂⟩ :=
    exists_positive_max_eigenpair U hUs hUc hU0 hUnonneg
  have he₂' : T (v₂ : E) = (μ₂ : 𝕜) • (v₂ : E) :=
    congrArg (fun z : V => (z : E)) he₂
  have hv₂' : ‖(v₂ : E)‖ = 1 := hv₂
  have hq₂ : T.reApplyInnerSelf (v₂ : E) = μ₂ := by
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, he₂',
      inner_smul_left, inner_self_eq_norm_sq_to_K, hv₂']
  have horder : μ₂ ≤ μ₁ := by
    have h := hfirst (v₂ : E)
    simpa only [hq₂, hv₂', one_pow, mul_one] using h
  refine ⟨μ₂, hμ₂, horder, (v₂ : E), hv₂', ?_, he₂', ?_⟩
  · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp v₂.property
  · intro z hz
    have hzV : z ∈ V := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hz
    exact quadratic_bound_of_rayleigh_bound U hb₂ (⟨z, hzV⟩ : V)

end Torsion.CompactSelfAdjoint

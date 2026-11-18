module

public import Torsion.Proof.PaperBoundaryAttainment

@[expose] public section

/-! # The largest classical boundary slope equals the original weak gradient norm -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace Torsion

/-- For any torsion representative smooth across the boundary, the true
gradient norm reaches its global maximum on the boundary, where its inward
normal derivative also attains this value. -/
theorem DirichletTheory.exists_classical_boundary_slope_maximum (T : DirichletTheory)
    (D : ConvexDomain) {v : Plane → ℝ} {N : Set Plane} (hN : IsOpen N)
    (hcl : closure D.carrier ⊆ N) (hv : ContDiffOn ℝ 1 v N)
    (hrep : (T.solution D).value =ᵐ[volume.restrict D.carrier] v) :
    ∃ p ∈ frontier D.carrier, ∃ n : Plane, ‖n‖ = 1 ∧
      (∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) n (z - p)) ∧
      fderiv ℝ v p n = (T.G D).toReal ∧ ‖gradient v p‖ = (T.G D).toReal ∧
      ∀ x ∈ closure D.carrier, ‖gradient v x‖ ≤ (T.G D).toReal := by
  obtain ⟨s⟩ := T.exists_maximizingNormalSequence D
  have hsmall : D.carrier ⊆ N := subset_closure.trans hcl
  have heq : EqOn s.value v D.carrier := Measure.eqOn_open_of_ae_eq
    (s.value_eq.symm.trans hrep) D.isOpen s.continuous.continuousOn (hv.continuousOn.mono hsmall)
  have hclose := heq.of_subset_closure s.continuous.continuousOn
    (hv.continuousOn.mono hcl) subset_closure Subset.rfl
  have hgrad : ContinuousOn (gradient v) (closure D.carrier) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
      ((hv.continuousOn_fderiv_of_isOpen hN (by simp)).mono hcl)
  have hb (x : Plane) (hx : x ∈ closure D.carrier) : ‖gradient v x‖ ≤ (T.G D).toReal := by
    apply le_on_closure (s := D.carrier) _ hgrad.norm continuousOn_const hx
    intro z hz
    have hlocal : s.value =ᶠ[𝓝 z] v := heq.eventuallyEq_of_mem (D.isOpen.mem_nhds hz)
    rw [norm_gradient_eq_fderiv, ← hlocal.fderiv_eq]
    exact norm_fderiv_le_of_lipschitz ℝ s.lipschitz
  have hp := frontier_subset_closure s.point_mem
  have hv0 : v s.point = 0 := by
    rw [← hclose hp, s.zero_off _]
    exact (D.isOpen.frontier_eq ▸ s.point_mem).2
  have hdiff := ((hv.differentiableOn (by norm_num)) s.point (hcl hp)).differentiableAt (hN.mem_nhds (hcl hp))
  have hline : HasDerivAt (fun t : ℝ => s.point + t • s.normal) s.normal 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s.normal).const_add s.point
  have hdiff' : HasFDerivAt v (fderiv ℝ v s.point) (s.point + (0 : ℝ) • s.normal) := by
    simpa using hdiff.hasFDerivAt
  have hd := hdiff'.comp_hasDerivAt 0 hline
  have hnorm : Tendsto (fun t : ℝ => v (s.point + t • s.normal) / t) (𝓝[>] 0)
      (𝓝 (fderiv ℝ v s.point s.normal)) := by
    simpa [Function.comp_def, hv0, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right
  have hsame : (fun t : ℝ => s.value (s.point + t • s.normal) / t) =ᶠ[𝓝[>] 0]
      (fun t : ℝ => v (s.point + t • s.normal) / t) := by
    filter_upwards [s.fixed_normal_enters s.rectangleComparison] with t ht using congrArg (· / t) (heq ht)
  have he := tendsto_nhds_unique (hnorm.congr' hsame.symm) (s.fixed_normal_quotient s.rectangleComparison)
  refine ⟨s.point, s.point_mem, s.normal, s.unit, s.support, he, le_antisymm (hb _ hp) ?_, hb⟩
  calc
    (T.G D).toReal = fderiv ℝ v s.point s.normal := he.symm
    _ ≤ ‖fderiv ℝ v s.point s.normal‖ := le_abs_self _
    _ ≤ ‖fderiv ℝ v s.point‖ * ‖s.normal‖ := (fderiv ℝ v s.point).le_opNorm _
    _ = _ := by rw [s.unit, mul_one, norm_gradient_eq_fderiv]

end Torsion

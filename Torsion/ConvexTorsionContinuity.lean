import Torsion.NormalFrame
import Torsion.ConvexSupportingPoint
import Torsion.WeakTorsionRepresentative
import Torsion.SlabTorsionBarrier
import Torsion.BoundaryCollarGradient

/-!
# Genuine continuous zero extension on every original convex domain

Nearest supporting points and orthogonal covariance reduce the actual slab
barrier to a uniform distance bound. Together with interior regularity this
constructs boundary continuity without a smooth-boundary trace theorem.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion

/-- A finite uniform linear distance bound for any continuous interior
representative of actual convex-domain torsion. -/
theorem IsWeakTorsion.exists_distance_bound_on_representative
    {D : ConvexDomain} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D.carrier u g) (hU : ContinuousOn U D.carrier)
    (hrep : u =ᵐ[volume.restrict D.carrier] U) (hzero : ∀ x ∉ D.carrier, U x = 0) :
    ∃ L : ℝ≥0, ∀ x ∈ D.carrier, U x ≤ L * infDist x D.carrierᶜ := by
  have hweak := hu.of_zero_extension_representative D.isOpen.measurableSet hrep hzero
  obtain ⟨R, hR, hRD⟩ := D.bounded.closure.subset_ball_lt 0 (0 : Plane)
  let B : ℝ := 2 * R + 1
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨⟨B / 2, (half_pos hB).le⟩, ?_⟩
  intro x hx
  obtain ⟨p, hp, hd, hnorm, hn, hs⟩ := D.exists_nearest_supported_frontier hx
  let d : ℝ := infDist x D.carrierᶜ
  let n : Plane := d⁻¹ • (x - p)
  let e := normalFrame n hn
  let E := D.inNormalFrame p n hn
  let z : Plane := e.symm (x - p)
  have hpR : ‖p‖ < R := by
    simpa only [Metric.mem_ball, dist_zero_right] using hRD (frontier_subset_closure hp)
  have hslab : ∀ w ∈ E.carrier, 0 < w.im ∧ w.im < B := by
    intro w hw
    have hwD := (D.mem_inNormalFrame p n w hn).mp hw
    have hwR : ‖e w + p‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hRD (subset_closure hwD)
    have hnormw : ‖w‖ < 2 * R := by
      calc
        ‖w‖ = ‖e w‖ := (e.norm_map w).symm
        _ = ‖(e w + p) - p‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖e w + p‖ + ‖p‖ := norm_sub_le _ _
        _ < 2 * R := by linarith
    refine ⟨D.inNormalFrame_subset_upper p n hn hs hw, ?_⟩
    exact (Complex.im_le_norm w).trans_lt (hnormw.trans (by dsimp [B]; linarith))
  have hEC : ContinuousOn (fun w => U (e w + p)) E.carrier :=
    hU.comp (e.continuous.add continuous_const).continuousOn
      (fun w hw => (D.mem_inNormalFrame p n w hn).mp hw)
  have hzD : z ∈ E.carrier := by
    apply (D.mem_inNormalFrame p n z hn).mpr
    change e z + p ∈ D.carrier
    simpa only [z, LinearIsometryEquiv.apply_symm_apply, sub_add_cancel] using hx
  have hbd := (hweak.inNormalFrame p n hn).le_slab_lower_linear_on_localRepresentative
    E.isOpen E.bounded hslab E.isOpen (Subset.rfl) hEC EventuallyEq.rfl z hzD
  have hzim : z.im = d := by
    rw [show z = (normalFrame n hn).symm (x - p) from rfl,
      normalFrame_symm_im, show n = d⁻¹ • (x - p) from rfl,
      real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm]
    change d⁻¹ * d ^ 2 = d
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]
  have hez : e z + p = x := by
    simp only [z, LinearIsometryEquiv.apply_symm_apply, sub_add_cancel]
  simpa only [hez, hzim, sub_zero, NNReal.coe_mk] using hbd

/-- The actual weak solution on every original convex domain admits a
globally continuous zero extension with smooth interior, preserving its
original value and weak-gradient classes. -/
theorem IsWeakTorsion.exists_continuous_smooth_representative
    {D : ConvexDomain} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D.carrier u g) :
    ∃ U : Plane → ℝ, Continuous U ∧ ContDiffOn ℝ ∞ U D.carrier ∧
      (∀ x ∉ D.carrier, U x = 0) ∧ (∀ x, 0 ≤ U x) ∧
      (u =ᵐ[volume.restrict D.carrier] U) ∧
      (g =ᵐ[volume.restrict D.carrier] gradient U) := by
  obtain ⟨U, hs, hzero, hrep, hgrad⟩ := hu.exists_smooth_representative D.isOpen D.bounded
  have hpos := hu.nonneg_on_representative D.isOpen D.bounded hs.continuousOn hrep
  obtain ⟨L, hL⟩ := hu.exists_distance_bound_on_representative hs.continuousOn hrep hzero
  have hc : Continuous U := continuous_of_zero_extension_boundary_collar
    D.isOpen hs.continuousOn hzero hpos (by norm_num : (0 : ℝ) < 1)
    (fun x hx _ => hL x hx)
  refine ⟨U, hc, hs, hzero, ?_, hrep, hgrad⟩
  intro x
  by_cases hx : x ∈ D.carrier
  · exact hpos x hx
  · rw [hzero x hx]

/-- Every actual bounded convex torsion solution has a global Lipschitz
zero-extension representative. The constant is constructed from a containing
ball; no boundary regularity is assumed. -/
theorem IsWeakTorsion.exists_lipschitz_representative
    {D : ConvexDomain} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D.carrier u g) :
    ∃ (L : ℝ≥0) (U : Plane → ℝ), LipschitzWith L U ∧
      ContDiffOn ℝ ∞ U D.carrier ∧ (∀ x ∉ D.carrier, U x = 0) ∧
      (∀ x, 0 ≤ U x) ∧ (u =ᵐ[volume.restrict D.carrier] U) ∧
      (g =ᵐ[volume.restrict D.carrier] gradient U) := by
  obtain ⟨U, hc, hs, hz, hp, hrep, hg⟩ := hu.exists_continuous_smooth_representative
  obtain ⟨L, hL⟩ := hu.exists_distance_bound_on_representative hs.continuousOn hrep hz
  refine ⟨L, U, ?_, hs, hz, hp, hrep, hg⟩
  exact hu.lipschitzWith_of_boundary_collar D.isOpen D.bounded hc hs hg hz hp
    (by norm_num : (0 : ℝ) < 1) (fun x hx _ => hL x hx)

/-- Finiteness concerns exactly the original interior essential supremum,
for every original admissible convex domain and every actual solution choice. -/
theorem DirichletTheory.G_lt_top (T : DirichletTheory) (D : ConvexDomain) :
    T.G D < ⊤ := by
  obtain ⟨L, U, hLip, _, _, _, hrep, _⟩ :=
    (T.solution D).weakEquation.exists_lipschitz_representative
  have hb := (T.solution D).weakEquation.eLpNorm_gradient_le_of_lipschitzOn
    D.isOpen D.bounded hLip.lipschitzOnWith hrep
  exact lt_of_le_of_lt hb ENNReal.coe_lt_top

end Torsion

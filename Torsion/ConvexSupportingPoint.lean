import Torsion.Definitions
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Actual supporting normals and nearest boundary points

Real Hahn--Banach separation and the Riesz isomorphism produce strict
inward support for every exterior point of an open convex domain. At a
nearest complement point, the maximal interior ball forces that normal to
be exactly the normalized displacement from the boundary to the center.
-/

noncomputable section
open Set Metric

namespace Torsion

/-- Strict support is constructed over the original concrete convex set,
including a genuine unit normal, rather than assumed as boundary data. -/
theorem ConvexDomain.exists_unit_inward_support (D : ConvexDomain) {p : Plane}
    (hp : p ∉ D.carrier) :
    ∃ n : Plane, ‖n‖ = 1 ∧ ∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) n (z - p) := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open D.convex D.isOpen hp
  let v : Plane := (InnerProductSpace.toDual ℝ Plane).symm f
  have hvinner (z : Plane) : inner (𝕜 := ℝ) v z = f z :=
    InnerProductSpace.toDual_symm_apply
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨z, hz⟩ := D.nonempty
    have h := hf z hz
    rw [← hvinner p, ← hvinner z, hv0] at h
    simp at h
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · simp [norm_smul, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv)), hv]
  · intro z hz
    rw [real_inner_smul_left, inner_sub_right, hvinner, hvinner]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hv)) (sub_pos.mpr (hf z hz))

/-- The original bounded admissible domain has a genuine exterior point. -/
theorem ConvexDomain.compl_nonempty (D : ConvexDomain) : D.carrierᶜ.Nonempty := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp D.bounded
  let y : Plane := ((max R 0 + 1 : ℝ) : Plane)
  refine ⟨y, ?_⟩
  intro hy
  have hh := hR y hy
  have hpos : 0 < max R 0 + 1 := by linarith [le_max_right R 0]
  simp only [y, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hh
  linarith [le_max_left R 0]

/-- There is an actual nearest frontier point and its inward normal is
the normalized physical displacement. All support inequalities are strict
throughout the original open domain. -/
theorem ConvexDomain.exists_nearest_supported_frontier (D : ConvexDomain)
    {x : Plane} (hx : x ∈ D.carrier) :
    ∃ p : Plane, p ∈ frontier D.carrier ∧
      0 < infDist x D.carrierᶜ ∧
      ‖x - p‖ = infDist x D.carrierᶜ ∧
      ‖(infDist x D.carrierᶜ)⁻¹ • (x - p)‖ = 1 ∧
      ∀ z ∈ D.carrier,
        0 < inner (𝕜 := ℝ) ((infDist x D.carrierᶜ)⁻¹ • (x - p)) (z - p) := by
  let d := infDist x D.carrierᶜ
  have hd : 0 < d :=
    (D.isOpen.isClosed_compl.not_mem_iff_infDist_pos D.compl_nonempty).mp
      (by simpa only [mem_compl_iff, not_not] using hx)
  obtain ⟨p, hp, hdist⟩ := D.isOpen.isClosed_compl.exists_infDist_eq_dist D.compl_nonempty x
  have hnorm : ‖x - p‖ = d := by simpa only [dist_eq_norm] using hdist.symm
  have hball : ball x d ⊆ D.carrier := ball_infDist_compl_subset
  have hclosed : closedBall x d ⊆ closure D.carrier := by
    rw [← closure_ball x hd.ne']
    exact closure_mono hball
  have hpcl : p ∈ closure D.carrier := by
    apply hclosed
    rw [mem_closedBall, dist_comm, ← hdist]
  have hpfront : p ∈ frontier D.carrier := by
    rw [D.isOpen.frontier_eq]
    exact ⟨hpcl, hp⟩
  obtain ⟨n, hn, hs⟩ := D.exists_unit_inward_support hp
  have hscl : ∀ z ∈ closure D.carrier, 0 ≤ inner (𝕜 := ℝ) n (z - p) := by
    have hclosedSupport : IsClosed {z : Plane | 0 ≤ inner (𝕜 := ℝ) n (z - p)} :=
      isClosed_le continuous_const (continuous_const.inner (continuous_id.sub continuous_const))
    exact hclosedSupport.closure_subset_iff.mpr (fun z hz => (hs z hz).le)
  have htouch : x - d • n ∈ closedBall x d := by
    rw [mem_closedBall, dist_eq_norm]
    simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hd, hn, mul_one]
    exact le_rfl
  have hlow : d ≤ inner (𝕜 := ℝ) n (x - p) := by
    have hh := hscl (x - d • n) (hclosed htouch)
    rw [show x - d • n - p = (x - p) - d • n by abel,
      inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hn] at hh
    simp only [one_pow, mul_one] at hh
    linarith
  have hupp : inner (𝕜 := ℝ) n (x - p) ≤ d := by
    simpa only [hn, hnorm, one_mul] using real_inner_le_norm n (x - p)
  have hinner : inner (𝕜 := ℝ) n (x - p) = d := le_antisymm hupp hlow
  have hvec : x - p = d • n := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hh := norm_sub_sq_real (x - p) (d • n)
    rw [hnorm, norm_smul, Real.norm_eq_abs, abs_of_pos hd, hn, mul_one,
      inner_smul_right, real_inner_comm n (x - p), hinner] at hh
    nlinarith [norm_nonneg ((x - p) - d • n)]
  have hnormalized : d⁻¹ • (x - p) = n := by
    rw [hvec, smul_smul, inv_mul_cancel₀ hd.ne', one_smul]
  refine ⟨p, hpfront, hd, hnorm, ?_, ?_⟩
  · change ‖d⁻¹ • (x - p)‖ = 1
    rw [hnormalized, hn]
  · change ∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) (d⁻¹ • (x - p)) (z - p)
    simpa only [hnormalized] using hs

/-- A fixed genuine interior ball has at least its own radius of height
above every supporting line with a unit inward normal. -/
theorem support_height_ge_of_ball {D : Set Plane} {a p n : Plane} {h : ℝ}
    (hh : 0 < h) (hball : ball a h ⊆ D) (hn : ‖n‖ = 1)
    (hs : ∀ z ∈ D, 0 ≤ inner (𝕜 := ℝ) n (z - p)) :
    h ≤ inner (𝕜 := ℝ) n (a - p) := by
  have hscl : closure D ⊆ {z : Plane | 0 ≤ inner (𝕜 := ℝ) n (z - p)} := by
    apply (isClosed_le continuous_const
      (continuous_const.inner (continuous_id.sub continuous_const))).closure_subset_iff.mpr
    exact hs
  have hclosed : closedBall a h ⊆ closure D := by
    rw [← closure_ball a hh.ne']
    exact closure_mono hball
  have htouch : a - h • n ∈ closedBall a h := by
    rw [mem_closedBall, dist_eq_norm]
    simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hh, hn, mul_one]
    exact le_rfl
  have hv := hscl (hclosed htouch)
  change 0 ≤ inner (𝕜 := ℝ) n (a - h • n - p) at hv
  rw [show a - h • n - p = (a - p) - h • n by abel,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hn] at hv
  simp only [one_pow, mul_one] at hv
  linarith

/-- A single actual inball gives positive uniform height and a uniform
displacement bound in every boundary supporting coordinate frame. -/
theorem ConvexDomain.exists_uniform_support_inball (D : ConvexDomain) :
    ∃ (a : Plane) (h M : ℝ), 0 < h ∧ 0 ≤ M ∧ a ∈ D.carrier ∧ ball a h ⊆ D.carrier ∧
      ∀ p ∈ frontier D.carrier, ∀ n : Plane, ‖n‖ = 1 →
        (∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) n (z - p)) →
        h ≤ inner (𝕜 := ℝ) n (a - p) ∧ ‖a - p‖ ≤ M := by
  obtain ⟨a, ha⟩ := D.nonempty
  obtain ⟨h, hh, hball⟩ := Metric.isOpen_iff.mp D.isOpen a ha
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp D.bounded.closure
  have hRnonneg : 0 ≤ R := (norm_nonneg a).trans (hR a (subset_closure ha))
  refine ⟨a, h, ‖a‖ + R, hh, add_nonneg (norm_nonneg _) hRnonneg, ha, hball, ?_⟩
  intro p hp n hn hs
  refine ⟨support_height_ge_of_ball hh hball hn (fun z hz => (hs z hz).le), ?_⟩
  exact (norm_sub_le a p).trans (add_le_add_left (hR p (frontier_subset_closure hp)) _)

end Torsion

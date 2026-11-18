module

public import Torsion.Proof.PaperBoundaryAttainment

@[expose] public section

/-! # The blow-up at a maximizing boundary slope

The sharp global Lipschitz constant is attained along one inward ray. At
the same point, supporting-plane comparison and comparison with increasingly
distant points of that ray determine the blow-up in every direction.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Torsion.MaximizingNormalSequence
variable {T : DirichletTheory} {D : ConvexDomain}

private theorem blowup_lipschitz (s : MaximizingNormalSequence T D) (z w : Plane)
    {ε : ℝ} (hε : 0 < ε) :
    |s.value (s.point + ε • z) / ε - s.value (s.point + ε • w) / ε| ≤
      (T.G D).toReal * ‖z-w‖ := by
  have h := s.lipschitz.dist_le_mul (s.point + ε • z) (s.point + ε • w)
  have he : s.point + ε • z - (s.point + ε • w) = ε • (z-w) := by rw [smul_sub]; abel
  rw [Real.dist_eq, dist_eq_norm, he, norm_smul, Real.norm_of_nonneg hε.le] at h
  rw [← sub_div, abs_div, abs_of_pos hε, div_le_iff₀ hε]
  change _ ≤ (T.G D).toReal * (ε * ‖z-w‖) at h
  linarith only [h, mul_assoc (T.G D).toReal ε ‖z-w‖,
    mul_comm ε ‖z-w‖, mul_assoc (T.G D).toReal ‖z-w‖ ε]

/-- This integrable local bound holds at all spatial scales and directions. -/
theorem blowup_abs_le (s : MaximizingNormalSequence T D) (z : Plane) {ε : ℝ} (hε : 0 < ε) :
    |s.value (s.point + ε • z) / ε| ≤ (T.G D).toReal * ‖z‖ := by
  have hp := s.point_mem
  rw [D.isOpen.frontier_eq] at hp
  simpa only [smul_zero, add_zero, s.zero_off _ hp.2, zero_div, sub_zero] using s.blowup_lipschitz z 0 hε

private theorem zero_behind_support (s : MaximizingNormalSequence T D) {w : Plane}
    (hw : inner ℝ s.normal w ≤ 0) {ε : ℝ} (hε : 0 < ε) : s.value (s.point + ε • w) = 0 := by
  apply s.zero_off
  intro hin
  have h := s.support _ hin
  rw [add_sub_cancel_left, real_inner_smul_right] at h
  exact h.not_ge (mul_nonpos_of_nonneg_of_nonpos hε.le hw)

private theorem blowup_upper (s : MaximizingNormalSequence T D) (z : Plane) {ε : ℝ} (hε : 0 < ε) :
    s.value (s.point + ε • z) / ε ≤ (T.G D).toReal * max 0 (inner ℝ s.normal z) := by
  let a := inner ℝ s.normal z
  by_cases ha : 0 ≤ a
  · let w := z - a • s.normal
    have hw : inner ℝ s.normal w = 0 := by
      simp only [w, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
        s.unit, one_pow, mul_one, a, sub_self]
    have hh := s.blowup_lipschitz z w hε
    have he : z-w = a • s.normal := by dsimp [w]; abel
    rw [s.zero_behind_support hw.le hε, zero_div, sub_zero, he, norm_smul, s.unit,
      mul_one, Real.norm_of_nonneg ha, abs_of_nonneg (div_nonneg (s.nonneg _) hε.le)] at hh
    change _ ≤ (T.G D).toReal * max 0 a
    rwa [max_eq_right ha]
  · rw [s.zero_behind_support (le_of_not_ge ha) hε, zero_div,
      max_eq_left (le_of_not_ge ha), mul_zero]

private theorem exists_far_normal {n z : Plane} (hn : ‖n‖ = 1) {d : ℝ}
    (hd : d < inner ℝ n z) : ∃ L : ℝ, 0 < L ∧ d < L - ‖z-L • n‖ := by
  let η := inner ℝ n z - d
  have hη : 0 < η := sub_pos.mpr hd
  let L := |d| + ‖z‖^2/(2*η) + 1
  have hpos : 0 < L := by dsimp [L]; positivity
  have hLd : 0 < L-d := by dsimp [L]; linarith [le_abs_self d, div_nonneg (sq_nonneg ‖z‖) (by positivity : 0 ≤ 2*η)]
  have hineq : ‖z‖^2 < 2*η*L := by
    have hh : ‖z‖^2/(2*η) < L := by dsimp [L]; linarith [abs_nonneg d]
    simpa [mul_comm] using (div_lt_iff₀ (by positivity : 0 < 2*η)).mp hh
  have hh := norm_sub_sq_real z (L • n)
  rw [norm_smul, Real.norm_of_nonneg hpos.le, hn, mul_one, real_inner_smul_right, ← real_inner_comm z n] at hh
  have hs : ‖z-L • n‖ < L-d := by
    apply (sq_lt_sq₀ (norm_nonneg _) hLd.le).mp
    change ‖z‖^2 < 2 * (inner ℝ n z - d) * L at hineq
    nlinarith [sq_nonneg d]
  exact ⟨L, hpos, by linarith⟩

/-- At a boundary point attaining the sharp Lipschitz constant, all rescaled
torsion values converge to the corresponding linear function on the inward
half-plane, extended by zero across the supporting line. -/
theorem blowup_tendsto (s : MaximizingNormalSequence T D) (z : Plane) :
    Tendsto (fun ε : ℝ => s.value (s.point + ε • z) / ε) (𝓝[>] 0)
      (𝓝 ((T.G D).toReal * max 0 (inner ℝ s.normal z))) := by
  let G := (T.G D).toReal
  have hG : 0 < G := T.G_toReal_pos D
  by_cases ha : 0 < inner ℝ s.normal z
  · rw [max_eq_right ha.le]
    apply tendsto_order.mpr
    constructor
    · intro b hb
      obtain ⟨L, hL, hfar⟩ := exists_far_normal (z := z) s.unit ((div_lt_iff₀ hG).mpr (by simpa [G, mul_comm] using hb))
      have hscale : Tendsto (fun ε : ℝ => ε * L) (𝓝[>] 0) (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨?_, ?_⟩
        · simpa using ((continuous_id.mul_const L).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ε hε using mul_pos hε hL
      have hnormal := (s.fixed_normal_quotient s.rectangleComparison).comp hscale
      have hlim : Tendsto (fun ε : ℝ => s.value (s.point + ε • (L • s.normal)) / ε - G*‖z-L • s.normal‖)
          (𝓝[>] 0) (𝓝 (G*L - G*‖z-L • s.normal‖)) := by
        apply ((hnormal.mul_const L).sub_const (G*‖z-L • s.normal‖)).congr'
        filter_upwards [self_mem_nhdsWithin] with ε hε
        simp only [Function.comp_apply, smul_smul]
        field_simp [hL.ne']
      have hb' : b < G*L - G*‖z-L • s.normal‖ := by
        have hh := (div_lt_iff₀ hG).mp hfar
        linarith only [hh, mul_sub G L ‖z-L • s.normal‖, mul_comm (L-‖z-L • s.normal‖) G]
      filter_upwards [hlim.eventually (lt_mem_nhds hb'), self_mem_nhdsWithin] with ε h hε
      have hh := s.blowup_lipschitz z (L • s.normal) hε
      linarith [(abs_le.mp hh).1]
    · intro b hb
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hh := s.blowup_upper z hε
      rw [max_eq_right ha.le] at hh
      exact hh.trans_lt hb
  · rw [max_eq_left (le_of_not_gt ha), mul_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [s.zero_behind_support (le_of_not_gt ha) hε, zero_div]

end Torsion.MaximizingNormalSequence

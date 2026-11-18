module

public import Torsion.ConvexGaugeRadial
public import Torsion.CauchyRadialDomain

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Radial representation at a flat mark (Lemma 6.2)

The last point of the closed domain on each ray determines the profile. Convexity
with the marked half-ball gives lower semicontinuity even on horizontal rays.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Torsion

private abbrev Angle := ContinuousProfiles.Angle

private def rayDirection (θ : Angle) : Plane := gaugeDirection θ

@[fun_prop] private theorem ray_continuous : Continuous rayDirection :=
  continuous_gaugeDirection.comp continuous_subtype_val

private theorem ray_norm (θ : Angle) : ‖rayDirection θ‖ = 1 := norm_gaugeDirection _

private theorem ray_im_nonneg (θ : Angle) : 0 ≤ (rayDirection θ).im := by
  simpa [rayDirection, gaugeDirection, Complex.exp_mul_I, Complex.sin_ofReal_re] using
    Real.sin_nonneg_of_mem_Icc θ.property

private theorem lower_ray_mem {K : Set Plane} (hc : Convex ℝ K)
    (hzero : (0 : Plane) ∈ K) {v : Plane} {t s : ℝ}
    (ht : t • v ∈ K) (hs : 0 ≤ s) (hst : s ≤ t) : s • v ∈ K := by
  have hseg : s ∈ segment ℝ (0 : ℝ) t :=
    Icc_subset_segment ⟨hs, hst⟩
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  simp only [smul_eq_mul, mul_zero, zero_add] at heq
  simpa only [smul_zero, zero_add, smul_smul, heq] using hc hzero ht ha hb hab

/-- For each angle, the largest radius whose point lies in the compact closure.
The maximum belongs to the ray, including at zero and pi. -/
private theorem exists_max_closed_ray (D : ConvexDomain) (hzero : (0 : Plane) ∈ closure D.carrier)
    (θ : Angle) : ∃ r : ℝ, IsGreatest {s : ℝ | 0 ≤ s ∧ s • rayDirection θ ∈ closure D.carrier} r := by
  let S := {s : ℝ | 0 ≤ s ∧ s • rayDirection θ ∈ closure D.carrier}
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp D.bounded.closure
  have hclosed : IsClosed S := isClosed_Ici.inter
    (isClosed_closure.preimage (continuous_id.smul continuous_const))
  apply (isCompact_Icc.of_isClosed_subset hclosed (show S ⊆ Icc 0 B from ?_)).exists_isGreatest
  · exact ⟨0, le_rfl, by simpa using hzero⟩
  · intro r hr
    refine ⟨hr.1, ?_⟩
    simpa only [norm_smul, Real.norm_of_nonneg hr.1, ray_norm, mul_one] using hB _ hr.2

private theorem marked_closed_halfBall (D : ConvexDomain) (hm : IsMarked D.carrier) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : Plane, 0 ≤ z.im → ‖z‖ < ρ → z ∈ closure D.carrier := by
  obtain ⟨ρ, hρ, hpatch⟩ := hm.2.2.2
  refine ⟨ρ, hρ, ?_⟩
  intro z him hn
  have hz : z ∈ closure upperHalfPlane := by
    simpa only [upperHalfPlane, Complex.closure_setOfPred_lt_im, mem_ofPred_eq] using him
  have hb : z ∈ ball (0 : Plane) ρ := by simpa only [mem_ball, dist_zero_right] using hn
  apply closure_mono (s := upperHalfPlane ∩ ball (0 : Plane) ρ) _ (isOpen_ball.closure_inter ⟨hz, hb⟩)
  rw [← hpatch]
  exact inter_subset_left

/-- Any strictly shorter positive radius persists on nearby rays. The displaced small
point varies in the closed upper half-ball. At a horizontal limiting ray its imaginary
part is automatically nonnegative, including for the endpoint direction itself. -/
private theorem eventually_shorter_ray {K : Set Plane} (hc : Convex ℝ K)
    {ρ : ℝ} (hρ : 0 < ρ) (hpatch : ∀ z : Plane, 0 ≤ z.im → ‖z‖ < ρ → z ∈ K)
    (θ : Angle) {r s : ℝ} (hr : r • rayDirection θ ∈ K) (hs : 0 < s) (hsr : s < r) :
    ∀ᶠ θ' in 𝓝 θ, s • rayDirection θ' ∈ K := by
  let u := min ρ s / 2
  have hu : 0 < u := half_pos (lt_min hρ hs)
  have hus : u < s := (half_lt_self (lt_min hρ hs)).trans_le (min_le_right ρ s)
  have huρ : u < ρ := (half_lt_self (lt_min hρ hs)).trans_le (min_le_left ρ s)
  obtain ⟨a, b, ha, hb, hab, heq⟩ := (Ioo_subset_openSegment ⟨hus, hsr⟩ :
    s ∈ openSegment ℝ u r)
  simp only [smul_eq_mul] at heq
  let W (φ : Angle) : Plane := a⁻¹ • (s • rayDirection φ - b • (r • rayDirection θ))
  have hW (φ : Angle) : a • W φ + b • (r • rayDirection θ) = s • rayDirection φ := by
    dsimp only [W]
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul, sub_add_cancel]
  have hcenter : W θ = u • rayDirection θ := by
    dsimp only [W]
    rw [smul_smul, ← sub_smul, smul_smul]
    congr 1
    rw [← heq, add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  have hcont : Continuous W := by
    dsimp only [W]
    fun_prop
  have hnorm : ∀ᶠ φ in 𝓝 θ, ‖W φ‖ < ρ := hcont.norm.continuousAt.eventually_lt
    continuousAt_const (by simpa only [hcenter, norm_smul, Real.norm_of_nonneg hu.le,
      ray_norm, mul_one] using huρ)
  have him : ∀ᶠ φ in 𝓝 θ, 0 ≤ (W φ).im := by
    rcases (ray_im_nonneg θ).eq_or_lt with h | h
    · filter_upwards [] with φ
      simp only [W, Complex.smul_im, Complex.sub_im, smul_eq_mul, ← h, mul_zero, sub_zero]
      exact mul_nonneg (inv_nonneg.mpr ha.le) (mul_nonneg hs.le (ray_im_nonneg φ))
    · have hp : 0 < (W θ).im := by
        simpa only [hcenter, Complex.smul_im, smul_eq_mul] using mul_pos hu h
      exact (continuousAt_const.eventually_lt (Complex.continuous_im.comp hcont).continuousAt hp).mono
        fun _ hpos => hpos.le
  filter_upwards [hnorm, him] with φ hn hi
  exact hW φ ▸ hc (hpatch _ hi hn) hr ha.le hb.le hab

/-- A positive continuous profile for a marked convex domain. Its horizontal
endpoint radii are precisely the two endpoints of the base in the closed domain. -/
theorem ConvexDomain.exists_marked_radial_profile (D : ConvexDomain) (hm : IsMarked D.carrier) :
    ∃ R : ContinuousProfiles.Profile, (∀ θ, 0 < R θ) ∧
      radialDomain (ContinuousProfiles.extend R) = D.carrier ∧
      ∀ A B : ℝ, (∀ x : ℝ, (x : Plane) ∈ closure D.carrier ↔ -B ≤ x ∧ x ≤ A) →
        R ⟨0, le_rfl, Real.pi_pos.le⟩ = A ∧ R ⟨Real.pi, Real.pi_pos.le, le_rfl⟩ = B := by
  classical
  obtain ⟨ρ, hρ, hpatch⟩ := marked_closed_halfBall D hm
  have hzero : (0 : Plane) ∈ closure D.carrier := hpatch _ (by simp) (by simpa using hρ)
  choose R hR using exists_max_closed_ray D hzero
  have hpos (θ : Angle) : 0 < R θ := by
    apply (half_pos hρ).trans_le
    apply (hR θ).2
    refine ⟨(half_pos hρ).le, hpatch _ ?_ ?_⟩
    · simpa only [Complex.smul_im, smul_eq_mul] using mul_nonneg (half_pos hρ).le (ray_im_nonneg θ)
    · simpa only [norm_smul, Real.norm_of_nonneg (half_pos hρ).le, ray_norm, mul_one]
        using half_lt_self hρ
  have hcont : Continuous R := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    apply tendsto_order.mpr
    constructor
    · intro l hl
      obtain ⟨s, hs, hsr⟩ := exists_between (max_lt hl (hpos θ))
      have hs0 : 0 < s := (le_max_right l 0).trans_lt hs
      filter_upwards [eventually_shorter_ray D.convex.closure hρ hpatch θ (hR θ).1.2 hs0 hsr] with φ hφ
      exact ((le_max_left l 0).trans_lt hs).trans_le ((hR φ).2 ⟨hs0.le, hφ⟩)
    · intro l hl
      have hl0 := (hpos θ).trans hl
      have hnot : l • rayDirection θ ∉ closure D.carrier :=
        fun hx => hl.not_ge ((hR θ).2 ⟨hl0.le, hx⟩)
      have hmap : Continuous (fun φ : Angle => l • rayDirection φ) := by
        fun_prop
      have hout : ∀ᶠ φ in 𝓝 θ, l • rayDirection φ ∉ closure D.carrier :=
        hmap.continuousAt (isClosed_closure.isOpen_compl.mem_nhds hnot)
      filter_upwards [hout] with φ hn
      exact lt_of_not_ge fun hle => hn (lower_ray_mem D.convex.closure hzero (hR φ).1.2 hl0.le hle)
  let P : ContinuousProfiles.Profile := ⟨R, hcont⟩
  refine ⟨P, hpos, hm.radialDomain_eq_of_frontier_radii D.convex P hpos ?_, ?_⟩
  · intro θ _ _
    change R θ • rayDirection θ ∈ frontier D.carrier
    rw [D.isOpen.frontier_eq]
    refine ⟨(hR θ).1.2, ?_⟩
    intro hx
    have ho : IsOpen {r : ℝ | r • rayDirection θ ∈ D.carrier} :=
      D.isOpen.preimage (continuous_id.smul continuous_const)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho _ hx
    have hlt : R θ < R θ + ε/2 := by linarith
    have hmem : R θ + ε/2 ∈ ball (R θ) ε := by
      rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    exact hlt.not_ge ((hR θ).2 ⟨((hpos θ).trans hlt).le, subset_closure (hball hmem)⟩)
  · intro A B hbase
    let θ₀ : Angle := ⟨0, le_rfl, Real.pi_pos.le⟩
    let θπ : Angle := ⟨Real.pi, Real.pi_pos.le, le_rfl⟩
    have hd₀ : rayDirection θ₀ = 1 := by simp [rayDirection, gaugeDirection, θ₀]
    have hdπ : rayDirection θπ = -1 := by simp [rayDirection, gaugeDirection, θπ, Complex.exp_pi_mul_I]
    have hbase₀ := (hbase 0).mp (by simpa using hzero)
    have hAB : -B ≤ A := hbase₀.1.trans hbase₀.2
    have hright : ((R θ₀ : ℝ) : Plane) ∈ closure D.carrier := by
      simpa only [hd₀, Complex.real_smul, mul_one] using (hR θ₀).1.2
    have hleft : ((-(R θπ) : ℝ) : Plane) ∈ closure D.carrier := by
      simpa only [hdπ, Complex.real_smul, mul_neg, mul_one, Complex.ofReal_neg] using (hR θπ).1.2
    constructor
    · apply le_antisymm ((hbase _).mp hright).2
      apply (hR θ₀).2
      refine ⟨hbase₀.2, ?_⟩
      simpa only [hd₀, Complex.real_smul, mul_one] using (hbase A).mpr ⟨hAB, le_rfl⟩
    · apply le_antisymm (neg_le_neg_iff.mp ((hbase _).mp hleft).1)
      apply (hR θπ).2
      refine ⟨by linarith [hbase₀.1], ?_⟩
      simpa only [hdπ, Complex.real_smul, mul_neg, mul_one, Complex.ofReal_neg] using
        (hbase (-B)).mpr ⟨le_rfl, hAB⟩

end Torsion

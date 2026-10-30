import Torsion.RadialFluxConcavity

/-!
# Transfer from finite step domains to continuous radial profiles

The only flux assumptions are the marked-domain order, homogeneity, and
supermodularity rules. Uniform approximation is supplied by finite small
closed-sector covers obtained from compactness of `[0, π]`.
-/

noncomputable section
namespace Torsion.RadialFluxConcavity

open Set Filter
open scoped Topology Pointwise

private theorem arg_mem_of_im_pos {z : ℂ} (hz : 0 < z.im) : z.arg ∈ Ioo 0 Real.pi := by
  constructor
  · refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) ?_
    intro heq
    have hi := (Complex.arg_eq_zero_iff.mp heq.symm).2
    linarith
  · exact Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')

/-- Physical radial-profile scaling agrees with actual complex-plane dilation. -/
theorem radialDomain_smul (R : ℝ → ℝ) (t : ℝ) (ht : 0 < t) :
    radialDomain (t • R) = t • radialDomain R := by
  have hmem : ∀ z : ℂ, t • z ∈ radialDomain (t • R) ↔ z ∈ radialDomain R := by
    intro z
    rw [RadialGeometry.mem_radialDomain_iff, RadialGeometry.mem_radialDomain_iff]
    have him : (t • z).im = t * z.im := by simp [Complex.real_smul]
    have harg : (t • z).arg = z.arg := Complex.arg_real_mul z ht
    have hn : ‖t • z‖ = t * ‖z‖ := by simp [norm_smul, abs_of_pos ht]
    simp only [him, harg, hn, Pi.smul_apply, smul_eq_mul,
      mul_pos_iff_of_pos_left ht, mul_lt_mul_left ht]
  ext z
  constructor
  · intro hz
    refine ⟨t⁻¹ • z, ?_, by simp [smul_smul, ht.ne']⟩
    apply (hmem (t⁻¹ • z)).mp
    simpa [smul_smul, ht.ne'] using hz
  · rintro ⟨w, hw, rfl⟩
    exact (hmem w).mpr hw

private theorem flux_bounds_of_samples {ι : Type*} [Fintype ι]
    (P : AngularCover ι) {Q : Set ℂ → ℝ} (hQ : MarkedFluxRules Q)
    {R : ℝ → ℝ} (hR : ContinuousOn R (Icc 0 Real.pi))
    (hpos : ∀ θ ∈ Icc 0 Real.pi, 0 < R θ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (happrox : ∀ θ ∈ Ioo 0 Real.pi, ∀ i,
      P.lower i ≤ θ ∧ θ ≤ P.upper i →
        (1 - ε) * R θ ≤ r i ∧ r i ≤ (1 + ε) * R θ) :
    (1 - ε) * Q (radialDomain R) ≤ Q (P.domain r) ∧
      Q (P.domain r) ≤ (1 + ε) * Q (radialDomain R) := by
  have hlow : 0 < 1 - ε := sub_pos.mpr hε1
  have hupp : 0 < 1 + ε := by linarith
  have hD := RadialGeometry.radialDomain_isMarked hR hpos
  have hDs := P.domain_isMarked hr
  have hDl : IsMarked (radialDomain ((1 - ε) • R)) :=
    RadialGeometry.radialDomain_isMarked (continuousOn_const.mul hR)
      (fun θ hθ => mul_pos hlow (hpos θ hθ))
  have hDu : IsMarked (radialDomain ((1 + ε) • R)) :=
    RadialGeometry.radialDomain_isMarked (continuousOn_const.mul hR)
      (fun θ hθ => mul_pos hupp (hpos θ hθ))
  have hl : radialDomain ((1 - ε) • R) ⊆ P.domain r := by
    intro z hz
    have hz' := (RadialGeometry.mem_radialDomain_iff _ _).mp hz
    exact ⟨hz'.1, fun i hi => hz'.2.trans_le
      (happrox z.arg (arg_mem_of_im_pos hz'.1) i hi).1⟩
  have hu : P.domain r ⊆ radialDomain ((1 + ε) • R) := by
    intro z hz
    obtain ⟨i, hi⟩ := P.covers z.arg (arg_mem_of_im_pos hz.1)
    exact (RadialGeometry.mem_radialDomain_iff _ _).mpr
      ⟨hz.1, (hz.2 i hi).trans_le (happrox z.arg (arg_mem_of_im_pos hz.1) i hi).2⟩
  have hlQ := hQ.mono hDl hDs hl
  have huQ := hQ.mono hDs hDu hu
  rw [radialDomain_smul _ _ hlow, hQ.homogeneous hD _ hlow] at hlQ
  rw [radialDomain_smul _ _ hupp, hQ.homogeneous hD _ hupp] at huQ
  exact ⟨hlQ, huQ⟩

private theorem finite_approximation {Q : Set ℂ → ℝ} (hQ : MarkedFluxRules Q)
    {R S : ℝ → ℝ} (hR : ContinuousOn R (Icc 0 Real.pi))
    (hS : ContinuousOn S (Icc 0 Real.pi))
    (hRp : ∀ θ ∈ Icc 0 Real.pi, 0 < R θ)
    (hSp : ∀ θ ∈ Icc 0 Real.pi, 0 < S θ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ qR qS qT : ℝ,
      ((1 - ε) * Q (radialDomain R) ≤ qR ∧ qR ≤ (1 + ε) * Q (radialDomain R)) ∧
      ((1 - ε) * Q (radialDomain S) ≤ qS ∧ qS ≤ (1 + ε) * Q (radialDomain S)) ∧
      ((1 - ε) * Q (radialDomain (a • R + b • S)) ≤ qT ∧
        qT ≤ (1 + ε) * Q (radialDomain (a • R + b • S))) ∧
      a * qR + b * qS ≤ qT := by
  classical
  obtain ⟨θR, hθR, hminR⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) Real.pi).Nonempty from ⟨0, le_rfl, Real.pi_pos.le⟩) hR
  obtain ⟨θS, hθS, hminS⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) Real.pi).Nonempty from ⟨0, le_rfl, Real.pi_pos.le⟩) hS
  let m := min (R θR) (S θS)
  have hm : 0 < m := lt_min (hRp θR hθR) (hSp θS hθS)
  have hmR : ∀ θ ∈ Icc 0 Real.pi, m ≤ R θ := fun θ hθ =>
    (min_le_left _ _).trans (hminR hθ)
  have hmS : ∀ θ ∈ Icc 0 Real.pi, m ≤ S θ := fun θ hθ =>
    (min_le_right _ _).trans (hminS hθ)
  obtain ⟨δR, hδR, hcR⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hR) (ε * m) (mul_pos hε hm)
  obtain ⟨δS, hδS, hcS⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hS) (ε * m) (mul_pos hε hm)
  let δ := min δR δS
  have hδ : 0 < δ := lt_min hδR hδS
  let Angle := Icc (0 : ℝ) Real.pi
  have hcover : Icc (0 : ℝ) Real.pi ⊆ ⋃ c : Angle, Metric.ball (c : ℝ) (δ / 2) := by
    intro θ hθ
    exact mem_iUnion.mpr ⟨⟨θ, hθ⟩, Metric.mem_ball_self (half_pos hδ)⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover
    (fun c : Angle => Metric.ball (c : ℝ) (δ / 2)) (fun _ => Metric.isOpen_ball) hcover
  have hscover : ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      ∃ c ∈ s, dist θ (c : ℝ) < δ / 2 := by
    intro θ hθ
    obtain ⟨c, hc⟩ := mem_iUnion.mp (hs hθ)
    obtain ⟨hcs, hball⟩ := mem_iUnion.mp hc
    exact ⟨c, hcs, hball⟩
  let P : AngularCover ↥s :=
    { lower := fun i => (i.val : ℝ) - δ / 2
      upper := fun i => (i.val : ℝ) + δ / 2
      covers := by
        intro θ hθ
        obtain ⟨c, hc, hdist⟩ := hscover θ ⟨hθ.1.le, hθ.2.le⟩
        refine ⟨⟨c, hc⟩, ?_⟩
        rw [Real.dist_eq, abs_lt] at hdist
        constructor <;> dsimp <;> linarith }
  let r : ↥s → ℝ := fun i => R i.val
  let u : ↥s → ℝ := fun i => S i.val
  have hr : ∀ i, 0 < r i := fun i => hRp i.val i.val.property
  have hu : ∀ i, 0 < u i := fun i => hSp i.val i.val.property
  have hdist : ∀ θ ∈ Ioo 0 Real.pi, ∀ i : ↥s,
      P.lower i ≤ θ ∧ θ ≤ P.upper i → dist (i.val : ℝ) θ < δ := by
    intro θ hθ i hi
    rw [Real.dist_eq, abs_lt]
    dsimp [P] at hi
    constructor <;> linarith [half_lt_self hδ]
  have happroxR : ∀ θ ∈ Ioo 0 Real.pi, ∀ i : ↥s,
      P.lower i ≤ θ ∧ θ ≤ P.upper i →
        (1 - ε) * R θ ≤ r i ∧ r i ≤ (1 + ε) * R θ := by
    intro θ hθ i hi
    have hc := hcR i.val i.val.property θ ⟨hθ.1.le, hθ.2.le⟩
      ((hdist θ hθ i hi).trans_le (min_le_left _ _))
    rw [Real.dist_eq] at hc
    have hmε := mul_le_mul_of_nonneg_left (hmR θ ⟨hθ.1.le, hθ.2.le⟩) hε.le
    have habs := abs_le.mp (hc.le.trans hmε)
    change (1 - ε) * R θ ≤ R i.val ∧ R i.val ≤ (1 + ε) * R θ
    constructor <;> linarith
  have happroxS : ∀ θ ∈ Ioo 0 Real.pi, ∀ i : ↥s,
      P.lower i ≤ θ ∧ θ ≤ P.upper i →
        (1 - ε) * S θ ≤ u i ∧ u i ≤ (1 + ε) * S θ := by
    intro θ hθ i hi
    have hc := hcS i.val i.val.property θ ⟨hθ.1.le, hθ.2.le⟩
      ((hdist θ hθ i hi).trans_le (min_le_right _ _))
    rw [Real.dist_eq] at hc
    have hmε := mul_le_mul_of_nonneg_left (hmS θ ⟨hθ.1.le, hθ.2.le⟩) hε.le
    have habs := abs_le.mp (hc.le.trans hmε)
    change (1 - ε) * S θ ≤ S i.val ∧ S i.val ≤ (1 + ε) * S θ
    constructor <;> linarith
  have hT : ContinuousOn (a • R + b • S) (Icc 0 Real.pi) :=
    (continuousOn_const.mul hR).add (continuousOn_const.mul hS)
  have hTp : ∀ θ ∈ Icc 0 Real.pi, 0 < (a • R + b • S) θ := by
    intro θ hθ
    change 0 < a * R θ + b * S θ
    by_cases hapos : 0 < a
    · exact add_pos_of_pos_of_nonneg (mul_pos hapos (hRp θ hθ))
        (mul_nonneg hb (hSp θ hθ).le)
    · have hbpos : 0 < b := by linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg ha (hRp θ hθ).le)
        (mul_pos hbpos (hSp θ hθ))
  have hru : ∀ i, 0 < (a • r + b • u) i := fun i =>
    hTp i.val i.val.property
  have happroxT : ∀ θ ∈ Ioo 0 Real.pi, ∀ i : ↥s,
      P.lower i ≤ θ ∧ θ ≤ P.upper i →
        (1 - ε) * (a • R + b • S) θ ≤ (a • r + b • u) i ∧
          (a • r + b • u) i ≤ (1 + ε) * (a • R + b • S) θ := by
    intro θ hθ i hi
    obtain ⟨hRl, hRu⟩ := happroxR θ hθ i hi
    obtain ⟨hSl, hSu⟩ := happroxS θ hθ i hi
    constructor
    · calc
        _ = a * ((1 - ε) * R θ) + b * ((1 - ε) * S θ) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hRl ha)
          (mul_le_mul_of_nonneg_left hSl hb)
    · calc
        _ ≤ a * ((1 + ε) * R θ) + b * ((1 + ε) * S θ) :=
          add_le_add (mul_le_mul_of_nonneg_left hRu ha) (mul_le_mul_of_nonneg_left hSu hb)
        _ = _ := by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨Q (P.domain r), Q (P.domain u), Q (P.domain (a • r + b • u)),
    flux_bounds_of_samples P hQ hR hRp r hr hε hε1 happroxR,
    flux_bounds_of_samples P hQ hS hSp u hu hε hε1 happroxS,
    flux_bounds_of_samples P hQ hT hTp _ hru hε hε1 happroxT, ?_⟩
  exact (P.flux_concaveOn hQ).2 hr hu ha hb hab

/-- Theorem 3.6: continuous radial marked flux is concave. All step-domain
geometry, finite-dimensional concavity, and uniform approximation are proved;
only the three underlying marked-domain PDE rules remain inputs. -/
theorem radial_flux_concavity {Q : Set ℂ → ℝ} (hQ : MarkedFluxRules Q)
    {R S : ℝ → ℝ} (hR : ContinuousOn R (Icc 0 Real.pi))
    (hS : ContinuousOn S (Icc 0 Real.pi))
    (hRp : ∀ θ ∈ Icc 0 Real.pi, 0 < R θ)
    (hSp : ∀ θ ∈ Icc 0 Real.pi, 0 < S θ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * Q (radialDomain R) + b * Q (radialDomain S) ≤
      Q (radialDomain (a • R + b • S)) := by
  let ε := fun n : ℕ => 1 / ((n : ℝ) + 2)
  have hε : ∀ n, 0 < ε n := by intro n; dsimp [ε]; positivity
  have hε1 : ∀ n, ε n < 1 := by
    intro n
    dsimp [ε]
    rw [div_lt_one (by positivity)]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have happrox := fun n => finite_approximation hQ hR hS hRp hSp ha hb hab (hε n) (hε1 n)
  choose qR qS qT hqR hqS hqT hconcave using happrox
  have hlimε : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hlim (c : ℝ) (q : ℕ → ℝ)
      (hlo : ∀ n, (1 - ε n) * c ≤ q n) (hup : ∀ n, q n ≤ (1 + ε n) * c) :
      Tendsto q atTop (𝓝 c) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hleft := (hone.sub hlimε).mul_const c
    have hright := (hone.add hlimε).mul_const c
    simp only [sub_zero, add_zero, one_mul] at hleft hright
    exact hleft.squeeze' hright (Eventually.of_forall hlo) (Eventually.of_forall hup)
  have hlimR := hlim _ qR (fun n => (hqR n).1) (fun n => (hqR n).2)
  have hlimS := hlim _ qS (fun n => (hqS n).1) (fun n => (hqS n).2)
  have hlimT := hlim _ qT (fun n => (hqT n).1) (fun n => (hqT n).2)
  exact le_of_tendsto_of_tendsto ((hlimR.const_mul a).add (hlimS.const_mul b)) hlimT
    (Eventually.of_forall hconcave)



/-- The positive continuous radial cone, retaining both endpoint values. -/
def positiveContinuousProfiles : Set (ℝ → ℝ) :=
  {R | ContinuousOn R (Icc 0 Real.pi) ∧ ∀ θ ∈ Icc 0 Real.pi, 0 < R θ}

/-- The positive continuous radial cone is convex. -/
theorem convex_positiveContinuousProfiles : Convex ℝ positiveContinuousProfiles := by
  intro R hR S hS a b ha hb hab
  refine ⟨(continuousOn_const.mul hR.1).add (continuousOn_const.mul hS.1), ?_⟩
  intro θ hθ
  change 0 < a * R θ + b * S θ
  by_cases hapos : 0 < a
  · exact add_pos_of_pos_of_nonneg (mul_pos hapos (hR.2 θ hθ))
      (mul_nonneg hb (hS.2 θ hθ).le)
  · have hbpos : 0 < b := by linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha (hR.2 θ hθ).le)
      (mul_pos hbpos (hS.2 θ hθ))

/-- Theorem 3.6 as an actual concavity predicate on continuous profiles. -/
theorem radial_flux_concaveOn {Q : Set ℂ → ℝ} (hQ : MarkedFluxRules Q) :
    ConcaveOn ℝ positiveContinuousProfiles (fun R => Q (radialDomain R)) := by
  refine ⟨convex_positiveContinuousProfiles, ?_⟩
  intro R hR S hS a b ha hb hab
  exact radial_flux_concavity hQ hR.1 hS.1 hR.2 hS.2 ha hb hab

end Torsion.RadialFluxConcavity

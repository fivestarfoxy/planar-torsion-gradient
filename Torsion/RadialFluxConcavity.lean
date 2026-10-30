module

public import Torsion.RadialGeometry
public import Torsion.RadialConcavity.Mollification
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Radial flux concavity from marked-domain rules

Finite closed angular covers give actual open step domains. At a shared
interface every incident radial constraint is imposed, so the radius there is
the minimum of its incident values. This is the slit convention of §3.6.
-/

noncomputable section
namespace Torsion.RadialFluxConcavity

open Set Filter MeasureTheory
open scoped Topology Pointwise

variable {ι : Type*} [Fintype ι]

/-- A finite closed-sector cover of the upper half-plane's angle interval.
Overlaps are allowed; an ordinary adjacent partition is a special case. -/
structure AngularCover (ι : Type*) where
  lower : ι → ℝ
  upper : ι → ℝ
  covers : ∀ θ ∈ Ioo 0 Real.pi, ∃ i, lower i ≤ θ ∧ θ ≤ upper i

namespace AngularCover

variable (P : AngularCover ι)

omit [Fintype ι] in
include P in
private theorem index_nonempty : Nonempty ι := by
  obtain ⟨i, _⟩ := P.covers (Real.pi / 2) ⟨half_pos Real.pi_pos, half_lt_self Real.pi_pos⟩
  exact ⟨i⟩

/-- The interface-correct step domain, in actual physical coordinates. -/
def domain (r : ι → ℝ) : Set ℂ :=
  {z | 0 < z.im ∧ ∀ i, P.lower i ≤ z.arg ∧ z.arg ≤ P.upper i → ‖z‖ < r i}

omit [Fintype ι] in
theorem domain_mono {r s : ι → ℝ} (hrs : r ≤ s) : P.domain r ⊆ P.domain s := by
  intro z hz
  exact ⟨hz.1, fun i hi => (hz.2 i hi).trans_le (hrs i)⟩

omit [Fintype ι] in
theorem domain_inf (r s : ι → ℝ) : P.domain (r ⊓ s) = P.domain r ∩ P.domain s := by
  ext z
  simp only [domain, mem_setOf_eq, mem_inter_iff, Pi.inf_apply, lt_min_iff]
  aesop

omit [Fintype ι] in
/-- A join may fill interface slits, so this relation is inclusion. -/
theorem union_subset_domain_sup (r s : ι → ℝ) :
    P.domain r ∪ P.domain s ⊆ P.domain (r ⊔ s) := by
  apply union_subset
  · exact P.domain_mono le_sup_left
  · exact P.domain_mono le_sup_right

private theorem arg_mem_of_im_pos {z : ℂ} (hz : 0 < z.im) : z.arg ∈ Ioo 0 Real.pi := by
  constructor
  · refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) ?_
    intro heq
    have hi := (Complex.arg_eq_zero_iff.mp heq.symm).2
    linarith
  · exact Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')

/-- Every step domain is open, including its sector interfaces. -/
theorem domain_isOpen (r : ι → ℝ) : IsOpen (P.domain r) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hH : ∀ᶠ w : ℂ in 𝓝 z, 0 < w.im :=
    continuous_const.continuousAt.eventually_lt Complex.continuous_im.continuousAt hz.1
  have harg : ContinuousAt Complex.arg z := Complex.continuousAt_arg (Or.inr hz.1.ne')
  have hconstraints : ∀ i, ∀ᶠ w : ℂ in 𝓝 z,
      P.lower i ≤ w.arg ∧ w.arg ≤ P.upper i → ‖w‖ < r i := by
    intro i
    by_cases hi : P.lower i ≤ z.arg ∧ z.arg ≤ P.upper i
    · exact (continuous_norm.continuousAt.eventually_lt continuous_const.continuousAt
        (hz.2 i hi)).mono fun w hw _ => hw
    · have hi' : z.arg < P.lower i ∨ P.upper i < z.arg := by
        by_cases hlow : P.lower i ≤ z.arg
        · exact Or.inr (lt_of_not_ge (fun hup => hi ⟨hlow, hup⟩))
        · exact Or.inl (lt_of_not_ge hlow)
      rcases hi' with hi' | hi'
      · exact (harg.eventually_lt continuous_const.continuousAt hi').mono fun w hw hwi =>
          False.elim (not_lt_of_ge hwi.1 hw)
      · exact (continuous_const.continuousAt.eventually_lt harg hi').mono fun w hw hwi =>
          False.elim (not_lt_of_ge hwi.2 hw)
  filter_upwards [hH, eventually_all.mpr hconstraints] with w hw hwi
  exact ⟨hw, hwi⟩

/-- Finite positivity gives a marked half-ball; angular coverage bounds the
outer domain. Both claims concern the actual step set. -/
theorem domain_isMarked {r : ι → ℝ} (hr : ∀ i, 0 < r i) : IsMarked (P.domain r) := by
  letI : Nonempty ι := P.index_nonempty
  obtain ⟨imin, _, hmin⟩ := Finset.univ.exists_min_image r Finset.univ_nonempty
  obtain ⟨imax, _, hmax⟩ := Finset.univ.exists_max_image r Finset.univ_nonempty
  refine ⟨P.domain_isOpen r, ?_, (fun _ hz => hz.1), r imin, hr imin, ?_⟩
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨r imax, ?_⟩
    intro z hz
    obtain ⟨i, hi⟩ := P.covers z.arg (arg_mem_of_im_pos hz.1)
    exact (hz.2 i hi).le.trans (hmax i (Finset.mem_univ i))
  · ext z
    constructor
    · rintro ⟨hz, hb⟩
      exact ⟨hz.1, hb⟩
    · rintro ⟨hz, hb⟩
      refine ⟨⟨hz, fun i _ => ?_⟩, hb⟩
      have hn : ‖z‖ < r imin := by simpa [Metric.mem_ball, dist_zero_right] using hb
      exact hn.trans_le (hmin i (Finset.mem_univ i))

omit [Fintype ι] in
private theorem smul_mem_domain_iff (r : ι → ℝ) (t : ℝ) (ht : 0 < t) (z : ℂ) :
    t • z ∈ P.domain (t • r) ↔ z ∈ P.domain r := by
  have him : (t • z).im = t * z.im := by simp [Complex.real_smul]
  have harg : (t • z).arg = z.arg := Complex.arg_real_mul z ht
  have hn : ‖t • z‖ = t * ‖z‖ := by simp [norm_smul, abs_of_pos ht]
  simp only [domain, mem_setOf_eq, him, harg, hn, Pi.smul_apply, smul_eq_mul,
    mul_pos_iff_of_pos_left ht, mul_lt_mul_iff_right₀ ht]

omit [Fintype ι] in
/-- Physical dilation, not an abstract action on domain labels. -/
theorem domain_smul (r : ι → ℝ) (t : ℝ) (ht : 0 < t) :
    P.domain (t • r) = t • P.domain r := by
  ext z
  constructor
  · intro hz
    refine ⟨t⁻¹ • z, ?_, by simp [smul_smul, ht.ne']⟩
    apply (P.smul_mem_domain_iff r t ht (t⁻¹ • z)).mp
    simpa [smul_smul, ht.ne'] using hz
  · rintro ⟨w, hw, rfl⟩
    exact (P.smul_mem_domain_iff r t ht w).mpr hw

end AngularCover

/-- The PDE properties which this transfer theorem uses. They concern actual
marked sets, and remain explicit inputs until the weak PDE results supply them. -/
structure MarkedFluxRules (Q : Set ℂ → ℝ) : Prop where
  mono : ∀ {D E}, IsMarked D → IsMarked E → D ⊆ E → Q D ≤ Q E
  homogeneous : ∀ {D}, IsMarked D → ∀ t : ℝ, 0 < t → Q (t • D) = t * Q D
  supermodular : ∀ {D E}, IsMarked D → IsMarked E →
    Q D + Q E ≤ Q (D ∪ E) + Q (D ∩ E)

private theorem marked_union {D E : Set ℂ} (hD : IsMarked D) (hE : IsMarked E) :
    IsMarked (D ∪ E) := by
  obtain ⟨hDo, hDb, hDH, rD, hrD, hDball⟩ := hD
  obtain ⟨hEo, hEb, hEH, rE, hrE, hEball⟩ := hE
  refine ⟨hDo.union hEo, hDb.union hEb, union_subset hDH hEH,
    min rD rE, lt_min hrD hrE, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hb⟩
    exact ⟨(union_subset hDH hEH) hz, hb⟩
  · rintro ⟨hz, hb⟩
    refine ⟨Or.inl ?_, hb⟩
    have hbD : z ∈ Metric.ball 0 rD :=
      Metric.ball_subset_ball (min_le_left rD rE) hb
    have hzD : z ∈ D ∩ Metric.ball 0 rD := by rw [hDball]; exact ⟨hz, hbD⟩
    exact hzD.1

namespace AngularCover

variable (P : AngularCover ι) {Q : Set ℂ → ℝ} (hQ : MarkedFluxRules Q)

include hQ in
/-- The step-domain flux inherits positive homogeneity from physical dilation. -/
theorem flux_homogeneous : RadialConcavity.Homogeneous (fun r => Q (P.domain r)) := by
  intro r hr t ht
  change Q (P.domain (t • r)) = t * Q (P.domain r)
  rw [P.domain_smul r t ht]
  exact hQ.homogeneous (P.domain_isMarked hr) t ht

include hQ in
/-- Lattice supermodularity on step radii follows from intersection equality
and the join inclusion which accounts for interface slits. -/
theorem flux_supermodular : RadialConcavity.Supermodular (fun r => Q (P.domain r)) := by
  intro r hr s hs
  have hDr := P.domain_isMarked hr
  have hDs := P.domain_isMarked hs
  have hsup : ∀ i, 0 < (r ⊔ s) i := fun i => lt_sup_of_lt_left (hr i)
  have hmono := hQ.mono (marked_union hDr hDs) (P.domain_isMarked hsup)
    (P.union_subset_domain_sup r s)
  have hsuper := hQ.supermodular hDr hDs
  rw [← P.domain_inf r s] at hsuper
  linarith



include hQ in
/-- The dilation sandwich proves continuity on the positive radius cone.
Finite minima and maxima of coordinate ratios give continuous lower and upper
bounds, so no PDE continuity theorem is assumed here. -/
theorem flux_continuousOn : ContinuousOn (fun r => Q (P.domain r))
    RadialConcavity.positiveOrthant := by
  intro r hr
  letI : Nonempty ι := P.index_nonempty
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  let lowerRatio := fun s : ι → ℝ => Finset.univ.inf' hne (fun i => s i / r i)
  let upperRatio := fun s : ι → ℝ => Finset.univ.sup' hne (fun i => s i / r i)
  have hratio : ∀ i : ι, Continuous (fun s : ι → ℝ => s i / r i) := by
    intro i
    have hc : Continuous (fun s : ι → ℝ => s i) := continuous_apply i
    exact hc.div_const (r i)
  have hlc : Continuous lowerRatio := Continuous.finset_inf'_apply hne
    (fun i _ => hratio i)
  have huc : Continuous upperRatio := Continuous.finset_sup'_apply hne
    (fun i _ => hratio i)
  have hself : (fun i => r i / r i) = (fun _ : ι => (1 : ℝ)) :=
    funext fun i => div_self (hr i).ne'
  have hlr : lowerRatio r = 1 := by
    dsimp [lowerRatio]
    rw [hself, Finset.inf'_const]
  have hur : upperRatio r = 1 := by
    dsimp [upperRatio]
    rw [hself, Finset.sup'_const]
  have hbounds : ∀ s ∈ RadialConcavity.positiveOrthant,
      lowerRatio s * Q (P.domain r) ≤ Q (P.domain s) ∧
      Q (P.domain s) ≤ upperRatio s * Q (P.domain r) := by
    intro s hs
    have hls : 0 < lowerRatio s := (Finset.lt_inf'_iff hne).mpr
      (fun i _ => div_pos (hs i) (hr i))
    have hus : 0 < upperRatio s := by
      let i : ι := Classical.arbitrary ι
      exact (div_pos (hs i) (hr i)).trans_le
        (Finset.le_sup' (fun i => s i / r i) (Finset.mem_univ i))
    have hlower : lowerRatio s • r ≤ s := by
      intro i
      exact (le_div_iff₀ (hr i)).mp
        (Finset.inf'_le (fun i => s i / r i) (Finset.mem_univ i))
    have hupper : s ≤ upperRatio s • r := by
      intro i
      exact (div_le_iff₀ (hr i)).mp
        (Finset.le_sup' (fun i => s i / r i) (Finset.mem_univ i))
    have hlQ := hQ.mono (P.domain_isMarked (fun i => mul_pos hls (hr i)))
      (P.domain_isMarked hs) (P.domain_mono hlower)
    have huQ := hQ.mono (P.domain_isMarked hs)
      (P.domain_isMarked (fun i => mul_pos hus (hr i))) (P.domain_mono hupper)
    have hlhom := P.flux_homogeneous hQ r hr (lowerRatio s) hls
    have huhom := P.flux_homogeneous hQ r hr (upperRatio s) hus
    change Q (P.domain (lowerRatio s • r)) = _ at hlhom
    change Q (P.domain (upperRatio s • r)) = _ at huhom
    change Q (P.domain (lowerRatio s • r)) ≤ Q (P.domain s) at hlQ
    change Q (P.domain s) ≤ Q (P.domain (upperRatio s • r)) at huQ
    rw [hlhom] at hlQ
    rw [huhom] at huQ
    exact ⟨hlQ, huQ⟩
  have htl : Tendsto (fun s => lowerRatio s * Q (P.domain r))
      (𝓝[RadialConcavity.positiveOrthant] r) (𝓝 (Q (P.domain r))) := by
    simpa only [hlr, one_mul] using
      ((hlc.tendsto r).mul_const (Q (P.domain r))).mono_left nhdsWithin_le_nhds
  have htu : Tendsto (fun s => upperRatio s * Q (P.domain r))
      (𝓝[RadialConcavity.positiveOrthant] r) (𝓝 (Q (P.domain r))) := by
    simpa only [hur, one_mul] using
      ((huc.tendsto r).mul_const (Q (P.domain r))).mono_left nhdsWithin_le_nhds
  exact htl.squeeze' htu
    (by filter_upwards [self_mem_nhdsWithin] with s hs; exact (hbounds s hs).1)
    (by filter_upwards [self_mem_nhdsWithin] with s hs; exact (hbounds s hs).2)

include hQ in
/-- The source's finite step-profile concavity, deduced from marked-domain
monotonicity, physical homogeneity and supermodularity. -/
theorem flux_concaveOn : ConcaveOn ℝ RadialConcavity.positiveOrthant
    (fun r => Q (P.domain r)) :=
  RadialConcavity.concave_of_continuous_homogeneous_supermodular
    (P.flux_continuousOn hQ) (P.flux_homogeneous hQ) (P.flux_supermodular hQ)

end AngularCover
end Torsion.RadialFluxConcavity

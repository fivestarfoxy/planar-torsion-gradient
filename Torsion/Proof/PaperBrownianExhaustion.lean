module

public import Torsion.ConvexSupportingPoint
public import Mathlib.Probability.Process.HittingTime

@[expose] public section

/-! # Exhaustion of a bounded open domain along a continuous path -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace Torsion.Brownian

variable {Ω : Type*}

/-- Exit after time zero, allowing an infinite lifetime. -/
def pathExitTime (D : Set Plane) (X : ℝ≥0 → Ω → Plane) : Ω → ℝ≥0∞ :=
  hittingAfter X Dᶜ 0

/-- Finite observation time stopped at the first exit. -/
def cappedExit (D : Set Plane) (X : ℝ≥0 → Ω → Plane) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (t : ℝ≥0∞) (pathExitTime D X ω)).toNNReal

theorem coe_cappedExit (D : Set Plane) (X : ℝ≥0 → Ω → Plane) (t : ℝ≥0) (ω : Ω) :
    (cappedExit D X t ω : ℝ≥0∞) = min (t : ℝ≥0∞) (pathExitTime D X ω) :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))

theorem path_mem_before_cappedExit {D : Set Plane} {X : ℝ≥0 → Ω → Plane}
    {s t : ℝ≥0} {ω : Ω} (hs : s < cappedExit D X t ω) : X s ω ∈ D := by
  by_contra h
  have hle : pathExitTime D X ω ≤ s := hittingAfter_le_of_mem (bot_le : (0 : ℝ≥0) ≤ _) h
  have hlt : (s : ℝ≥0∞) < cappedExit D X t ω := ENNReal.coe_lt_coe.mpr hs
  rw [coe_cappedExit] at hlt
  exact (not_lt_of_ge hle) (lt_min_iff.mp hlt).2

/-- A continuous path with a finite first exit attains the closed complement. -/
theorem pathExitTime_mem_compl {D : Set Plane} {X : ℝ≥0 → Ω → Plane} {ω : Ω}
    (ho : IsOpen D) (hc : Continuous (fun t => X t ω))
    (hfin : pathExitTime D X ω ≠ ⊤) :
    X (pathExitTime D X ω).toNNReal ω ∈ Dᶜ := by
  have hex : ∃ j : ℝ≥0, 0 ≤ j ∧ X j ω ∈ Dᶜ := by
    by_contra! h
    apply hfin
    exact hittingAfter_eq_top_iff.mpr h
  let S := {j : ℝ≥0 | 0 ≤ j ∧ X j ω ∈ Dᶜ}
  have hcl : IsClosed S := isClosed_Ici.inter (ho.isClosed_compl.preimage hc)
  have hmem := hcl.csInf_mem (show S.Nonempty from hex) (OrderBot.bddBelow S)
  change X (ENNReal.toNNReal (hittingAfter X Dᶜ 0 ω)) ω ∈ Dᶜ
  rw [hittingAfter, ite_eq_left hex]
  exact hmem.2

/-- Points at positive distance from the complement, with the threshold tending to zero. -/
def innerDomain (D : Set Plane) (n : ℕ) : Set Plane :=
  {z | 1 / ((n : ℝ) + 1) < infDist z Dᶜ}

theorem innerDomain_isOpen (D : Set Plane) (n : ℕ) : IsOpen (innerDomain D n) :=
  isOpen_lt continuous_const (continuous_infDist_pt Dᶜ)

theorem closure_innerDomain_subset (D : Set Plane) (n : ℕ) :
    closure (innerDomain D n) ⊆ D := by
  have hsub : closure (innerDomain D n) ⊆ {z | 1 / ((n : ℝ) + 1) ≤ infDist z Dᶜ} :=
    closure_minimal (fun _ hz => (show 1 / ((n : ℝ) + 1) < _ from hz).le) (isClosed_le continuous_const (continuous_infDist_pt Dᶜ))
  intro z hz
  by_contra h
  have hh := hsub hz
  change 1 / ((n : ℝ) + 1) ≤ infDist z Dᶜ at hh
  rw [infDist_zero_of_mem h] at hh
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem capped_inner_le_exit {D : Set Plane} {X : ℝ≥0 → Ω → Plane} {ω : Ω}
    (ho : IsOpen D) (hc : Continuous (fun t => X t ω)) (hfin : pathExitTime D X ω ≠ ⊤)
    (n : ℕ) (t : ℝ≥0) :
    cappedExit (innerDomain D n) X t ω ≤ (pathExitTime D X ω).toNNReal := by
  apply ENNReal.coe_le_coe.mp
  rw [coe_cappedExit, ENNReal.coe_toNNReal hfin]
  apply (min_le_right _ _).trans
  have hout := pathExitTime_mem_compl ho hc hfin
  have hout' : X (pathExitTime D X ω).toNNReal ω ∉ innerDomain D n :=
    fun h => hout (closure_innerDomain_subset D n (subset_closure h))
  have hh : pathExitTime (innerDomain D n) X ω ≤ ((pathExitTime D X ω).toNNReal : ℝ≥0∞) :=
    hittingAfter_le_of_mem (u := X) (n := (0 : ℝ≥0)) (s := (innerDomain D n)ᶜ) bot_le hout'
  rwa [ENNReal.coe_toNNReal hfin] at hh

/-- Every compact time interval strictly before exit is eventually contained in
the time interval preceding the capped exits from the inner domains. -/
theorem eventually_lt_capped_inner {D : Set Plane} {X : ℝ≥0 → Ω → Plane} {ω : Ω}
    (ho : IsOpen D) (hcomp : Dᶜ.Nonempty) (hc : Continuous (fun t => X t ω))
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < pathExitTime D X ω) :
    ∀ᶠ n : ℕ in atTop, s < cappedExit (innerDomain D n) X n ω := by
  have hpath (r : ℝ≥0) (hr : r ∈ Icc 0 s) : X r ω ∈ D := by
    by_contra h
    have hle : pathExitTime D X ω ≤ r := hittingAfter_le_of_mem (bot_le : (0 : ℝ≥0) ≤ _) h
    have hlt := (ENNReal.coe_le_coe.mpr hr.2).trans_lt hs
    exact (not_lt_of_ge hle) hlt
  let d (r : ℝ≥0) := infDist (X r ω) Dᶜ
  have hdc : Continuous d := (continuous_infDist_pt Dᶜ).comp hc
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (bot_le : (0 : ℝ≥0) ≤ s))
    hdc.continuousOn
  have hdr : 0 < d r := (ho.isClosed_compl.notMem_iff_infDist_pos hcomp).mp
    (notMem_compl_iff.mpr (hpath r hr))
  have he := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hdr))
  have hsn : ∀ᶠ n : ℕ in atTop, s < (n : ℝ≥0) := tendsto_natCast_atTop_atTop.eventually
    (eventually_gt_atTop s)
  filter_upwards [he, hsn] with n hn hns
  by_contra! h
  have htime := coe_cappedExit (innerDomain D n) X n ω
  have hlt : (cappedExit (innerDomain D n) X n ω : ℝ≥0∞) < ((n : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_lt_coe.mpr (h.trans_lt hns)
  rw [htime] at hlt
  have hsmall : pathExitTime (innerDomain D n) X ω < (n : ℝ≥0) := (min_lt_iff.mp hlt).resolve_left (lt_irrefl _)
  have hfinite := ne_top_of_lt hsmall
  have heq : cappedExit (innerDomain D n) X n ω =
      (pathExitTime (innerDomain D n) X ω).toNNReal := by
    unfold cappedExit
    rw [min_eq_right hsmall.le]
  have hout := pathExitTime_mem_compl (innerDomain_isOpen D n) hc hfinite
  rw [← heq] at hout
  apply hout
  exact hn.trans_le (hmin ⟨bot_le, h⟩)

/-- Capped exits from the inner exhaustion tend pathwise to the full finite exit. -/
theorem capped_inner_tendsto_exit {D : Set Plane} {X : ℝ≥0 → Ω → Plane} {ω : Ω}
    (ho : IsOpen D) (hcomp : Dᶜ.Nonempty) (hc : Continuous (fun t => X t ω))
    (hfin : pathExitTime D X ω ≠ ⊤) :
    Tendsto (fun n : ℕ => cappedExit (innerDomain D n) X n ω) atTop
      (𝓝 (pathExitTime D X ω).toNNReal) := by
  apply tendsto_order.mpr
  constructor
  · intro s hs
    apply eventually_lt_capped_inner ho hcomp hc
    exact (ENNReal.coe_toNNReal hfin) ▸ ENNReal.coe_lt_coe.mpr hs
  · intro s hs
    exact Eventually.of_forall (fun n => (capped_inner_le_exit ho hc hfin n n).trans_lt hs)

end Torsion.Brownian

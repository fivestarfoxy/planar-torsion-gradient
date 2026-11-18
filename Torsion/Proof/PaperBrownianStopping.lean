module

public import Torsion.Proof.PaperBrownianExhaustion
public import Torsion.Proof.PaperBrownianModel
public import Torsion.WeakHarmonicRegularity
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! # First exit and the Brownian martingale problem for one-half the Laplacian

The local martingale problem is stated for all twice differentiable functions
and relatively compact open subdomains. Exhausting the domain gives the mean
first exit time from a bounded domain for the zero-boundary Poisson solution.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace Torsion.Brownian

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}

/-- The generator compensator following the path up to its exit from V. -/
def compensatedTest (X : ℝ≥0 → Ω → Plane) (V : Set Plane) (f : Plane → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  f (X (cappedExit V X t ω) ω) -
    (1 / 2) * ∫ s in (0 : ℝ)..(cappedExit V X t ω : ℝ),
      WeakHarmonicRegularity.planarLaplacian f (X s.toNNReal ω)

/-- The continuous martingale-problem convention for planar Brownian motion
with generator one-half the Euclidean Laplacian. Localization is only on
open subdomains with compact closure inside the differentiability domain. -/
def LocalLaplacianMartingaleProblem (X : ℝ≥0 → Ω → Plane)
    (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) : Prop :=
  ∀ (U V : Set Plane) (f : Plane → ℝ), IsOpen U → IsOpen V → IsCompact (closure V) →
    closure V ⊆ U → ContDiffOn ℝ 2 f U → Martingale (compensatedTest X V f) ℱ P

omit m in
theorem compensatedTest_poisson {X : ℝ≥0 → Ω → Plane} {U V : Set Plane}
    {f : Plane → ℝ} (hVU : V ⊆ U)
    (hΔ : ∀ z ∈ U, WeakHarmonicRegularity.planarLaplacian f z = -1)
    (t : ℝ≥0) (ω : Ω) :
    compensatedTest X V f t ω =
      f (X (cappedExit V X t ω) ω) + (cappedExit V X t ω : ℝ) / 2 := by
  let a := cappedExit V X t ω
  have hi : (∫ s in (0 : ℝ)..(a : ℝ), WeakHarmonicRegularity.planarLaplacian f
      (X s.toNNReal ω)) = ∫ _ in (0 : ℝ)..(a : ℝ), (-1 : ℝ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le a.coe_nonneg
    intro s hs
    have hst : s.toNNReal < a := by
      apply NNReal.coe_lt_coe.mp
      rw [Real.coe_toNNReal _ hs.1.le]
      exact hs.2
    exact hΔ _ (hVU (path_mem_before_cappedExit (t := t) hst))
  change f (X a ω) - 1 / 2 * _ = f (X a ω) + (a : ℝ) / 2
  rw [hi, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

/-- A localized compensated C² test has constant expectation at every deterministic time. -/
theorem compensatedTest_expectation [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → Plane}
    {ℱ : Filtration ℝ≥0 m} {V : Set Plane} {f : Plane → ℝ}
    (htest : Martingale (compensatedTest X V f) ℱ P)
    {x : Plane} (hstart : ∀ᵐ ω ∂P, X 0 ω = x) (t : ℝ≥0) :
    (∫ ω, compensatedTest X V f t ω ∂P) = f x := by
  have heq := htest.setIntegral_eq (i := (0 : ℝ≥0)) (j := t) bot_le
    (@MeasurableSet.univ _ (ℱ 0))
  rw [setIntegral_univ, setIntegral_univ] at heq
  rw [← heq]
  have hzero (ω : Ω) : compensatedTest X V f 0 ω = f (X 0 ω) := by
    simp [compensatedTest, cappedExit]
  simp_rw [hzero]
  calc
    (∫ ω, f (X 0 ω) ∂P) = ∫ _, f x ∂P := integral_congr_ae (hstart.mono fun _ h => congrArg f h)
    _ = _ := by simp

/-- For the Brownian martingale problem, the finite mean lifetime is twice
the continuous zero-boundary solution of the torsion equation. -/
theorem meanExitTime_eq_twice_of_localMartingale [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → Plane} {ℱ : Filtration ℝ≥0 m}
    (hgen : LocalLaplacianMartingaleProblem X ℱ P)
    {D : Set Plane} (ho : IsOpen D) (hb : Bornology.IsBounded D) (hcomp : Dᶜ.Nonempty)
    {x : Plane} (hstart : ∀ᵐ ω ∂P, X 0 ω = x)
    (hpaths : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hfin : ∀ᵐ ω ∂P, pathExitTime D X ω ≠ ⊤)
    (hint : Integrable (fun ω => (pathExitTime D X ω).toReal) P)
    {f : Plane → ℝ} (hc : Continuous f) (hs : ContDiffOn ℝ 2 f D)
    (hz : ∀ z ∉ D, f z = 0)
    (hΔ : ∀ z ∈ D, WeakHarmonicRegularity.planarLaplacian f z = -1) :
    (∫ ω, (pathExitTime D X ω).toReal ∂P) = 2 * f x := by
  let F (n : ℕ) := compensatedTest X (innerDomain D n) f (n : ℝ≥0)
  have htest (n : ℕ) : Martingale (compensatedTest X (innerDomain D n) f) ℱ P :=
    hgen D _ f ho (innerDomain_isOpen D n)
      ((hb.subset (subset_closure.trans (closure_innerDomain_subset D n))).isCompact_closure)
      (closure_innerDomain_subset D n) hs
  have hF (n : ℕ) (ω : Ω) : F n ω = f (X (cappedExit (innerDomain D n) X n ω) ω) +
      (cappedExit (innerDomain D n) X n ω : ℝ) / 2 :=
    compensatedTest_poisson (subset_closure.trans (closure_innerDomain_subset D n)) hΔ _ _
  have he (n : ℕ) : (∫ ω, F n ω ∂P) = f x :=
    compensatedTest_expectation (htest n) hstart n
  obtain ⟨K, hK⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hc.continuousOn
  have hbound (z : Plane) : ‖f z‖ ≤ max K 0 := by
    by_cases h : z ∈ D
    · exact (hK z (subset_closure h)).trans (le_max_left _ _)
    · simpa only [hz z h, norm_zero] using le_max_right K (0 : ℝ)
  have hlim := tendsto_integral_of_dominated_convergence (μ := P)
    (F := F) (f := fun ω => (pathExitTime D X ω).toReal / 2)
    (fun ω => max K 0 + (pathExitTime D X ω).toReal / 2)
    (fun n => ((htest n).integrable n).aestronglyMeasurable)
    ((integrable_const _).add (hint.div_const 2)) (fun n => ?_) ?_
  · have hconst : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 (f x)) := by
      simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop _)
    have heq := tendsto_nhds_unique hlim hconst
    rw [integral_div] at heq
    linarith
  · filter_upwards [hpaths, hfin] with ω hp ht
    rw [hF]
    have hle : (cappedExit (innerDomain D n) X n ω : ℝ) ≤ (pathExitTime D X ω).toReal :=
      capped_inner_le_exit ho hp ht n n
    calc
      _ ≤ ‖f (X (cappedExit (innerDomain D n) X n ω) ω)‖ +
          ‖(cappedExit (innerDomain D n) X n ω : ℝ) / 2‖ := norm_add_le _ _
      _ ≤ _ := by
        have ht0 : 0 ≤ (cappedExit (innerDomain D n) X n ω : ℝ) / 2 := by positivity
        rw [Real.norm_of_nonneg ht0]
        exact add_le_add (hbound _) (by linarith)
  · filter_upwards [hpaths, hfin] with ω hp ht
    have htime := capped_inner_tendsto_exit ho hcomp hp ht
    have hvalue := ((hc.comp hp).continuousAt.tendsto).comp htime
    have hzero := hz _ (pathExitTime_mem_compl ho hp ht)
    have hrealtime := NNReal.continuous_coe.continuousAt.tendsto.comp htime
    simpa only [hF, Function.comp_apply, hzero, zero_add, ENNReal.coe_toNNReal_eq_toReal] using
      hvalue.add (hrealtime.div_const 2)

end Torsion.Brownian

module

public import Torsion.Proof.PaperBrownianStopping
public import Torsion.Proof.PaperWeakPoisson

@[expose] public section

/-! # Mean Brownian lifetime of the actual torsion domain -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace Torsion.Brownian

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Almost sure exit and first-moment finiteness follow from the martingale problem
alone. The nonnegative Poisson solution gives a nonnegative compensated test.
Its limit is infinite on paths that never exit, so Fatou rules out those paths. -/
theorem lifetime_finite_of_localMartingale
    {X : ℝ≥0 → Ω → Plane} {ℱ : Filtration ℝ≥0 m}
    (hgen : LocalLaplacianMartingaleProblem X ℱ P)
    {D : Set Plane} (ho : IsOpen D) (hb : Bornology.IsBounded D) (hcomp : Dᶜ.Nonempty)
    {x : Plane} (hstart : ∀ᵐ ω ∂P, X 0 ω = x)
    (hpaths : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    {f : Plane → ℝ} (hc : Continuous f) (hs : ContDiffOn ℝ 2 f D)
    (hz : ∀ z ∉ D, f z = 0) (hpos : ∀ z, 0 ≤ f z)
    (hΔ : ∀ z ∈ D, WeakHarmonicRegularity.planarLaplacian f z = -1) :
    (∀ᵐ ω ∂P, pathExitTime D X ω ≠ ⊤) ∧ Integrable (fun ω => (pathExitTime D X ω).toReal) P := by
  let F (n : ℕ) := compensatedTest X (innerDomain D n) f (n : ℝ≥0)
  let A (n : ℕ) (ω : Ω) := ENNReal.ofReal (2 * F n ω)
  have htest (n : ℕ) : Martingale (compensatedTest X (innerDomain D n) f) ℱ P :=
    hgen D _ f ho (innerDomain_isOpen D n)
      ((hb.subset (subset_closure.trans (closure_innerDomain_subset D n))).isCompact_closure)
      (closure_innerDomain_subset D n) hs
  have hF (n : ℕ) (ω : Ω) : F n ω = f (X (cappedExit (innerDomain D n) X n ω) ω) +
      (cappedExit (innerDomain D n) X n ω : ℝ) / 2 :=
    compensatedTest_poisson (subset_closure.trans (closure_innerDomain_subset D n)) hΔ _ _
  have hmeas (n : ℕ) : AEMeasurable (A n) P := ENNReal.measurable_ofReal.comp_aemeasurable
    ((htest n).integrable n |>.const_mul (2 : ℝ) |>.aemeasurable)
  have hval (n : ℕ) : (∫⁻ ω, A n ω ∂P) = ENNReal.ofReal (2 * f x) := by
    change (∫⁻ ω, ENNReal.ofReal (2 * F n ω) ∂P) = _
    rw [← ofReal_integral_eq_lintegral_ofReal (((htest n).integrable n).const_mul 2) ?_,
      integral_const_mul, compensatedTest_expectation (htest n) hstart]
    apply Eventually.of_forall
    intro ω
    change 0 ≤ 2 * F n ω
    rw [hF]
    exact mul_nonneg (by norm_num) (add_nonneg (hpos _) (by positivity))
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => A n ω) atTop (𝓝 (pathExitTime D X ω)) := by
    filter_upwards [hpaths] with ω hp
    by_cases hfinite : pathExitTime D X ω = ⊤
    · rw [hfinite]
      apply ENNReal.tendsto_ofReal_atTop.comp
      apply Filter.tendsto_atTop.mpr
      intro a
      have ht : (a.toNNReal : ℝ≥0∞) < pathExitTime D X ω := by simp [hfinite]
      filter_upwards [eventually_lt_capped_inner ho hcomp hp ht] with n hn
      change a ≤ 2 * F n ω
      rw [hF]
      have hh : a ≤ (cappedExit (innerDomain D n) X n ω : ℝ) :=
        (Real.le_coe_toNNReal a).trans (NNReal.coe_le_coe.mpr hn.le)
      linarith [hpos (X (cappedExit (innerDomain D n) X n ω) ω)]
    · have ht := capped_inner_tendsto_exit ho hcomp hp hfinite
      have hv := ((hc.comp hp).continuousAt.tendsto).comp ht
      have hzero := hz _ (pathExitTime_mem_compl ho hp hfinite)
      have htr := NNReal.continuous_coe.continuousAt.tendsto.comp ht
      have hlimF := (hv.add (htr.div_const 2)).const_mul 2
      have hlimR : Tendsto (fun n => 2 * F n ω) atTop (𝓝 (pathExitTime D X ω).toReal) := by
        simpa only [hF, Function.comp_apply, hzero, zero_add, ENNReal.coe_toNNReal_eq_toReal,
          mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hlimF
      simpa only [A, Function.comp_def, ENNReal.ofReal_toReal hfinite] using
        (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlimR)
  have hme := ENNReal.aemeasurable_of_tendsto hmeas hlim
  have hle : (∫⁻ ω, pathExitTime D X ω ∂P) ≤ ENNReal.ofReal (2 * f x) := by
    calc
      _ = ∫⁻ ω, liminf (fun n => A n ω) atTop ∂P :=
        lintegral_congr_ae (hlim.mono fun _ h => h.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ ω, A n ω ∂P) atTop := lintegral_liminf_le' hmeas
      _ = _ := by simp only [hval, liminf_const]
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  exact ⟨(ae_lt_top' hme hfin).mono fun _ h => h.ne, integrable_toReal_of_lintegral_ne_top hme hfin⟩

/-- One continuous zero-extension representative of the actual weak torsion
solution gives the expected Brownian first exit at every starting point.
A continuous process is specified by its local C² martingale problem for Δ/2. -/
theorem expected_exitTime_eq_twice_weakTorsion (T : DirichletTheory) (D : ConvexDomain) :
    ∃ U : Plane → ℝ, Continuous U ∧ IsWeakTorsion D.carrier U (T.solution D).weakGradient ∧
      (∀ z ∉ D.carrier, U z = 0) ∧
      ((T.solution D).value =ᵐ[volume.restrict D.carrier] U) ∧
      ∀ (x : Plane) (X : ℝ≥0 → Ω → Plane) (ℱ : Filtration ℝ≥0 m),
        (∀ᵐ ω ∂P, X 0 ω = x) → (∀ᵐ ω ∂P, Continuous (fun t => X t ω)) →
        LocalLaplacianMartingaleProblem X ℱ P →
        (∀ᵐ ω ∂P, pathExitTime D.carrier X ω ≠ ⊤) ∧
        Integrable (fun ω => (pathExitTime D.carrier X ω).toReal) P ∧
        (∫ ω, (pathExitTime D.carrier X ω).toReal ∂P) = 2 * U x := by
  have hu := (T.solution D).weakEquation
  obtain ⟨U, hc, hs, hz, hp, hrep, hg⟩ := hu.exists_continuous_smooth_representative
  have hs₂ : ContDiffOn ℝ 2 U D.carrier := hs.of_le (by decide)
  have hΔ := hu.planarLaplacian_representative D.isOpen hs hg
  refine ⟨U, hc, hu.of_zero_extension_representative D.isOpen.measurableSet hrep hz,
    hz, hrep, ?_⟩
  intro x X ℱ hstart hpaths hgen
  obtain ⟨hτ, hI⟩ := lifetime_finite_of_localMartingale hgen D.isOpen D.bounded
    D.compl_nonempty hstart hpaths hc hs₂ hz hp hΔ
  exact ⟨hτ, hI, meanExitTime_eq_twice_of_localMartingale hgen D.isOpen D.bounded
    D.compl_nonempty hstart hpaths hτ hI hc hs₂ hz hΔ⟩

end Torsion.Brownian

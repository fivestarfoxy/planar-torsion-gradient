module

public import Torsion.RestrictedSpectralBarrierComparison
public import Torsion.RestrictedSpectralSemicircle

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Actual endpoint bounds from the concrete semicircle weak barrier. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion.Spectral

/-- The short-interval maximum principle gives a square-root boundary
bound once the concrete semicircle's original weak equation is available.
No boundedness or endpoint continuity of the eigenfunction is used. -/
theorem IsRestrictedEigenfunction.exists_semicircle_bound_of_weak_barrier
    {a : ℝ} {φ : ℝ → ℝ} (hEig : IsRestrictedEigenfunction a φ)
    (hb : MemRestrictedFormDomain semicircleBarrier)
    (hbarrier : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      energy semicircleBarrier ψ = ∫ x : ℝ, ψ x)
    (hφ : ContinuousOn φ (Ioo (-1 : ℝ) 1)) (hodd : Function.Odd φ)
    (hleft : ∀ x : ℝ, x ≤ 0 → φ x ≤ 0)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |φ x| ≤ C * semicircleBarrier x := by
  have ha : 0 < a := hEig.eigenvalue_pos
  have hlim : Tendsto (fun t : ℝ => a * semicircleBarrier t) (𝓝 1) (𝓝 0) := by
    simpa only [semicircleBarrier, one_pow, sub_self, max_self, Real.sqrt_zero, mul_zero] using
      (continuous_const.mul semicircleBarrier_continuous).tendsto (1 : ℝ)
  obtain ⟨ε, hε, hεbound⟩ := Metric.eventually_nhds_iff.mp
    (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  let δ : ℝ := min (ε / 2) (min (1 / 2) (Real.pi / (8 * a)))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδhalf : δ ≤ (1 / 2 : ℝ) := (min_le_right _ _).trans (min_le_left _ _)
  have hδa : δ ≤ Real.pi / (8 * a) := (min_le_right _ _).trans (min_le_right _ _)
  let r : ℝ := 1 - δ
  have hr0 : 0 < r := by dsimp only [r]; linarith
  have hr1 : r < 1 := by dsimp only [r]; linarith
  have hsmall : a < Real.pi / (4 * (1 - r)) := by
    apply (lt_div_iff₀ (by dsimp only [r]; linarith : 0 < 4 * (1 - r))).2
    have hh : δ * (8 * a) ≤ Real.pi := (le_div_iff₀ (by positivity : 0 < 8 * a)).mp hδa
    dsimp only [r]
    nlinarith [Real.pi_pos]
  have hbsmall (t : ℝ) (ht : t ∈ Icc r 1) : a * semicircleBarrier t ≤ 1 := by
    apply (hεbound ?_).le
    rw [Real.dist_eq, abs_of_nonpos (by linarith [ht.2] : t - 1 ≤ 0)]
    dsimp only [r] at ht
    linarith [ht.1]
  have hbpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) r) : 0 < semicircleBarrier t := by
    apply semicircleBarrier_pos
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans_lt hr1
  have hratio : ContinuousOn (fun t => φ t / semicircleBarrier t) (Icc (0 : ℝ) r) := by
    apply (hφ.mono ?_).div semicircleBarrier_continuous.continuousOn
      (fun t ht => (hbpos t ht).ne')
    intro t ht
    exact ⟨by linarith [ht.1], ht.2.trans_lt hr1⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hratio
  let C : ℝ := max M 0 + 1
  have hC : 0 < C := by dsimp only [C]; linarith [le_max_right M 0]
  have hMC : M ≤ C := by dsimp only [C]; linarith [le_max_left M 0]
  have hcompact (t : ℝ) (ht : t ∈ Icc (0 : ℝ) r) : φ t ≤ C * semicircleBarrier t := by
    have hh : φ t / semicircleBarrier t ≤ C :=
      ((le_abs_self _).trans (hM t ht)).trans hMC
    exact (div_le_iff₀ (hbpos t ht)).mp hh
  have hout (t : ℝ) (ht : t ∉ Icc r 1) : φ t ≤ C * semicircleBarrier t := by
    by_cases ht0 : t ≤ 0
    · exact (hleft t ht0).trans (mul_nonneg hC.le (semicircleBarrier_nonneg t))
    · by_cases ht1 : 1 ≤ t
      · rw [hzero t (ht1.trans (le_abs_self t))]
        exact mul_nonneg hC.le (semicircleBarrier_nonneg t)
      · apply hcompact t
        constructor
        · exact le_of_not_ge ht0
        · exact le_of_not_gt (fun hrt => ht ⟨hrt.le, (lt_of_not_ge ht1).le⟩)
  have hupperAE := hEig.le_mul_of_small_support_barrier hb hbarrier hC.le
    (show r < 1 from hr1) hsmall (ae_of_all _ hout) hbsmall
  have hpartAE : (fun t => max (φ t - C * semicircleBarrier t) 0) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [hupperAE] with t ht
    exact max_eq_right (sub_nonpos.mpr ht)
  have hpart : EqOn (fun t => max (φ t - C * semicircleBarrier t) 0)
      (fun _ => 0) (Ioo (-1 : ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq (μ := volume) (ae_restrict_of_ae hpartAE) isOpen_Ioo
      ((hφ.sub (continuousOn_const.mul semicircleBarrier_continuous.continuousOn)).sup continuousOn_const)
      continuousOn_const
  have hupper (t : ℝ) : φ t ≤ C * semicircleBarrier t := by
    by_cases ht : |t| < 1
    · have hh := le_max_left (φ t - C * semicircleBarrier t) 0
      have hhzero : max (φ t - C * semicircleBarrier t) 0 = 0 := hpart (abs_lt.mp ht)
      rw [hhzero] at hh
      linarith
    · rw [hzero t (le_of_not_gt ht)]
      exact mul_nonneg hC.le (semicircleBarrier_nonneg t)
  refine ⟨C, hC, fun t => abs_le.2 ⟨?_, hupper t⟩⟩
  have hh := hupper (-t)
  rw [hodd t, semicircleBarrier_even t] at hh
  linarith

/-- A concrete semicircle bound upgrades interior continuity to genuine
global continuity of the original zero-exterior representative. -/
theorem continuous_of_semicircle_bound {φ : ℝ → ℝ} {C : ℝ}
    (hφ : ContinuousOn φ (Ioo (-1 : ℝ) 1))
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hbound : ∀ x : ℝ, |φ x| ≤ C * semicircleBarrier x) : Continuous φ := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : |x| < 1
  · exact hφ.continuousAt (isOpen_Ioo.mem_nhds (abs_lt.mp hx))
  · have hx1 : 1 ≤ |x| := le_of_not_gt hx
    change Tendsto φ (𝓝 x) (𝓝 (φ x))
    rw [hzero x hx1]
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero, Real.norm_eq_abs]
    apply squeeze_zero (fun t => abs_nonneg _) hbound
    simpa only [semicircleBarrier_zero_exterior x hx1, mul_zero] using
      (continuous_const.mul semicircleBarrier_continuous).tendsto x

end Torsion.Spectral

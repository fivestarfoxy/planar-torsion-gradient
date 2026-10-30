module

public import Torsion.SpectralDefinitions
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-!
# Compact primitives for zero-mean restricted tests

An actual smooth test in the restricted core, with integral zero, is the
derivative of another test in that same core. The support remains strictly
inside the interval; this is not a boundary-trace assumption.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion.Spectral

/-- The actual restricted smooth core is closed under real linear
combinations, with the support controlled inside the original interval. -/
theorem IsCore.linear_combination {ψ ρ : ℝ → ℝ} (hψ : IsCore ψ) (hρ : IsCore ρ)
    (c d : ℝ) : IsCore (fun x => c * ψ x + d * ρ x) := by
  refine ⟨(contDiff_const.mul hψ.1).add (contDiff_const.mul hρ.1),
    hψ.2.1.mul_left.add hρ.2.1.mul_left, ?_⟩
  intro x hx
  rcases tsupport_add (fun x => c * ψ x) (fun x => d * ρ x) hx with hx | hx
  · exact hψ.2.2 (tsupport_mul_subset_right hx)
  · exact hρ.2.2 (tsupport_mul_subset_right hx)

/-- A restricted core test has support in a smaller closed interval. -/
theorem IsCore.exists_support_interval {ψ : ℝ → ℝ} (hψ : IsCore ψ) :
    ∃ l r : ℝ, -1 < l ∧ l < r ∧ r < 1 ∧ tsupport ψ ⊆ Ioo l r := by
  by_cases hs : (tsupport ψ).Nonempty
  · obtain ⟨a, ha⟩ := hψ.2.1.exists_isLeast hs
    obtain ⟨b, hb⟩ := hψ.2.1.exists_isGreatest hs
    have haI := hψ.2.2 ha.1
    have hbI := hψ.2.2 hb.1
    have hab : a ≤ b := ha.2 hb.1
    refine ⟨(a - 1) / 2, (b + 1) / 2, ?_, ?_, ?_, ?_⟩
    · linarith [haI.1]
    · linarith [haI.1, hbI.2]
    · linarith [hbI.2]
    · intro x hx
      have hax := ha.2 hx
      have hxb := hb.2 hx
      constructor <;> linarith [haI.1, hbI.2]
  · refine ⟨-(1 / 2), 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    exact fun x hx => (hs ⟨x, hx⟩).elim

/-- A normalized genuine smooth core test, useful for separating the
constant part of a distribution on the interval. -/
theorem exists_core_integral_one :
    ∃ ρ : ℝ → ℝ, IsCore ρ ∧ (∫ x : ℝ, ρ x) = 1 := by
  let B : ContDiffBump (0 : ℝ) :=
    ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  refine ⟨B.normed volume, ⟨B.contDiff_normed, B.hasCompactSupport_normed, ?_⟩,
    B.integral_normed⟩
  rw [B.tsupport_normed_eq]
  intro x hx
  have hx' : |x| ≤ (1 / 2 : ℝ) := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hx
  have habs := abs_le.mp hx'
  constructor <;> linarith [habs.1, habs.2]

/-- A zero-mean test has a smooth primitive whose support is still compact
and strictly inside the restricted interval. -/
theorem IsCore.exists_primitive_of_integral_eq_zero {ψ : ℝ → ℝ}
    (hψ : IsCore ψ) (hmean : (∫ x : ℝ, ψ x) = 0) :
    ∃ P : ℝ → ℝ, IsCore P ∧ deriv P = ψ := by
  classical
  obtain ⟨l, r, hl, hlr, hr, hsupp⟩ := hψ.exists_support_interval
  let P : ℝ → ℝ := fun x => ∫ t in l..x, ψ t
  have hd (x : ℝ) : HasDerivAt P (ψ x) x := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hψ.1.continuous.intervalIntegrable l x)
      (hψ.1.continuous.stronglyMeasurableAtFilter volume (𝓝 x))
      hψ.1.continuous.continuousAt
  have hderiv : deriv P = ψ := funext fun x => (hd x).deriv
  have hcont : ContDiff ℝ ∞ P := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x => (hd x).differentiableAt, ?_⟩
    rw [hderiv]
    exact hψ.1
  have hz (x : ℝ) (hx : x ∉ Ioo l r) : ψ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
  have hleft (x : ℝ) (hx : x ≤ l) : P x = 0 := by
    dsimp [P]
    calc
      (∫ t in l..x, ψ t) = ∫ t in l..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_ge hx] at ht
        exact hz t (fun h => (not_lt_of_ge ht.2) h.1)
      _ = 0 := by simp
  have hPr : P r = 0 := by
    change (∫ t in l..r, ψ t) = 0
    calc
      (∫ t in l..r, ψ t) = ∫ t : ℝ, ψ t :=
        intervalIntegral.integral_eq_integral_of_support_subset (μ := volume)
          (fun x hx => ⟨(hsupp (subset_tsupport ψ hx)).1,
            (hsupp (subset_tsupport ψ hx)).2.le⟩)
      _ = 0 := hmean
  have hright (x : ℝ) (hx : r ≤ x) : P x = 0 := by
    have hi : (∫ t in r..x, ψ t) = 0 := by
      calc
        (∫ t in r..x, ψ t) = ∫ t in r..x, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hx] at ht
          exact hz t (fun h => (not_lt_of_ge ht.1) h.2)
        _ = 0 := by simp
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hψ.1.continuous.intervalIntegrable l r)
      (hψ.1.continuous.intervalIntegrable r x)
    change P r + (∫ t in r..x, ψ t) = P x at hadd
    rw [hPr, hi] at hadd
    simpa using hadd.symm
  have hsupP : Function.support P ⊆ Icc l r := by
    intro x hx
    by_contra hnot
    have hnot' : x < l ∨ r < x := by
      simpa only [mem_Icc, not_and_or, not_le] using hnot
    rcases hnot' with hx' | hx'
    · exact hx (hleft x hx'.le)
    · exact hx (hright x hx'.le)
  have htsupP : tsupport P ⊆ Icc l r := closure_minimal hsupP isClosed_Icc
  refine ⟨P, ⟨hcont, ?_, ?_⟩, hderiv⟩
  · exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport P) htsupP
  · intro x hx
    have hx' := htsupP hx
    constructor <;> linarith [hx'.1, hx'.2]

end Torsion.Spectral

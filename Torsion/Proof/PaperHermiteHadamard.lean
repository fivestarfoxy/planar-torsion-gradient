module

public import Torsion.WeakHarmonicRegularity
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

/-! # Concentration and sharpness for the boundary Hermite–Hadamard coefficient

A smooth nonnegative density supported near a boundary point can be normalized
against arclength. Its weighted integral then recovers the normal slope at that
point. All functions and integrals are taken on the physical plane. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion.HermiteHadamard

/-- Concentrate smooth unit boundary mass at a prescribed point. Any measure that
gives positive mass to each neighborhood of this point within the compact set
works; in particular the construction applies to a curve's arclength measure. -/
theorem exists_smooth_concentrating_density {K : Set Plane} (hK : IsCompact K)
    (σ : Measure Plane) [IsFiniteMeasureOnCompacts σ] {p : Plane} (hp : p ∈ K)
    (hmass : ∀ r > 0, 0 < (σ.restrict K) (Metric.ball p r))
    {q : Plane → ℝ} (hq : ContinuousOn q K) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : Plane → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      (∀ x, 0 ≤ b x) ∧ Function.support b ⊆ Metric.ball p ε ∧
      (∫ x in K, b x ∂σ) = 1 ∧ |(∫ x in K, b x * q x ∂σ) - q p| < ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hq p hp) (ε / 2) (half_pos hε)
  let r := min δ ε
  have hr : 0 < r := lt_min hδ hε
  let χ : ContDiffBump p :=
    { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  let m := ∫ x in K, χ x ∂σ
  have hm : 0 < m := by
    apply (integral_pos_iff_support_of_nonneg χ.nonneg'
      (χ.continuous.continuousOn.integrableOn_compact hK)).2
    rw [χ.support_eq]
    exact hmass r hr
  let b := fun x => m⁻¹ * χ x
  have hb : ContDiff ℝ ∞ b := contDiff_const.mul χ.contDiff
  have hbc : HasCompactSupport b := χ.hasCompactSupport.mul_left
  have hb0 (x) : 0 ≤ b x := mul_nonneg (inv_nonneg.mpr hm.le) χ.nonneg
  have hs : Function.support b ⊆ Metric.ball p r := by
    intro x hx
    apply χ.support_eq.subset
    exact (mul_ne_zero_iff.mp hx).2
  have hunit : (∫ x in K, b x ∂σ) = 1 := by
    change (∫ x in K, m⁻¹ * χ x ∂σ) = 1
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hm.ne'
  refine ⟨b, hb, hbc, hb0, hs.trans (Metric.ball_subset_ball (min_le_right δ ε)), hunit, ?_⟩
  have hi := (hb.continuous.continuousOn.mul hq).integrableOn_compact (μ := σ) hK
  have hbI := hb.continuous.continuousOn.integrableOn_compact (μ := σ) hK
  have hpoint {x : Plane} (hx : x ∈ K) (hsup : b x ≠ 0) :
      |q x - q p| < ε / 2 := by
    have hd : dist x p < δ := (Metric.mem_ball.mp (hs hsup)).trans_le (min_le_left _ _)
    simpa only [Real.dist_eq] using hclose hx hd
  have hl : (q p - ε / 2) ≤ ∫ x in K, b x * q x ∂σ := by
    calc
      _ = ∫ x in K, b x * (q p - ε / 2) ∂σ := by rw [integral_mul_const, hunit, one_mul]
      _ ≤ _ := by
        apply setIntegral_mono_on (hbI.mul_const _) hi hK.measurableSet
        intro x hx
        by_cases h : b x = 0
        · simp [h]
        · apply mul_le_mul_of_nonneg_left _ (hb0 x)
          linarith [(abs_lt.mp (hpoint hx h)).1]
  have hu : (∫ x in K, b x * q x ∂σ) ≤ q p + ε / 2 := by
    calc
      _ ≤ ∫ x in K, b x * (q p + ε / 2) ∂σ := by
        apply setIntegral_mono_on hi (hbI.mul_const _) hK.measurableSet
        intro x hx
        by_cases h : b x = 0
        · simp [h]
        · apply mul_le_mul_of_nonneg_left _ (hb0 x)
          linarith [(abs_lt.mp (hpoint hx h)).2]
      _ = _ := by rw [integral_mul_const, hunit, one_mul]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The least coefficient for domination of the boundary-flux measure by
arclength is exactly the largest continuous normal slope. Smooth nonnegative
compactly supported traces suffice to detect it. -/
theorem boundary_coefficient_iff {K : Set Plane} (hK : IsCompact K)
    (σ : Measure Plane) [IsFiniteMeasureOnCompacts σ] {p : Plane} (hp : p ∈ K)
    (hmass : ∀ r > 0, 0 < (σ.restrict K) (Metric.ball p r))
    {q : Plane → ℝ} (hq : ContinuousOn q K) (hmax : ∀ x ∈ K, q x ≤ q p) (C : ℝ) :
    (∀ b : Plane → ℝ, ContDiff ℝ ∞ b → HasCompactSupport b → (∀ x, 0 ≤ b x) →
      (∫ x in K, b x * q x ∂σ) ≤ C * ∫ x in K, b x ∂σ) ↔ q p ≤ C := by
  constructor
  · intro h
    by_contra! hlt
    obtain ⟨b, hb, hbc, hb0, _, hone, hlim⟩ :=
      exists_smooth_concentrating_density hK σ hp hmass hq (sub_pos.mpr hlt)
    have hle := h b hb hbc hb0
    rw [hone, mul_one] at hle
    linarith [(abs_lt.mp hlim).1]
  · intro hC b hb _ hb0
    rw [← integral_const_mul]
    apply setIntegral_mono_on
      ((hb.continuous.continuousOn.mul hq).integrableOn_compact hK)
      ((continuousOn_const.mul hb.continuous.continuousOn).integrableOn_compact hK) hK.measurableSet
    intro x hx
    exact (mul_le_mul_of_nonneg_left ((hmax x hx).trans hC) (hb0 x)).trans_eq (mul_comm _ _)

end Torsion.HermiteHadamard

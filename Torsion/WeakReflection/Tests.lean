import Torsion.WeakReflection.Admission
import Torsion.WeakReflection
import Mathlib.Analysis.Calculus.MeanValue

/-! Admission of actual antisymmetric smooth tests on a flat half-domain. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace Torsion

theorem IsTest.exists_lipschitzWith {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) : ∃ C : ℝ≥0, LipschitzWith C ψ := by
  obtain ⟨C, hC⟩ := (hψ.1.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hψ.2.1.fderiv ℝ)
  refine ⟨⟨max C 0, le_max_right _ _⟩,
    lipschitzWith_of_nnnorm_fderiv_le (hψ.1.differentiable (by simp)) ?_⟩
  intro z
  exact_mod_cast (hC z).trans (le_max_left C 0)

/-- A compact smooth test odd across the real axis vanishes at least linearly
there. The coefficient is derived from its actual bounded derivative. -/
theorem IsTest.bound_by_im_of_antisymmetric {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) (hodd : ∀ z, ψ (star z) = -ψ z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |ψ z| ≤ C * |z.im| := by
  obtain ⟨C, hC⟩ := hψ.exists_lipschitzWith
  refine ⟨C, C.2, ?_⟩
  intro z
  have h := hC.dist_le_mul z (star z)
  have hn : ‖z - star z‖ = 2 * |z.im| := by
    change ‖z - (starRingEnd ℂ) z‖ = _
    rw [Complex.sub_conj]
    simp [norm_mul, abs_mul]
  rw [dist_eq_norm, dist_eq_norm, hodd z] at h
  have hv : ‖ψ z - -ψ z‖ = 2 * |ψ z| := by
    rw [sub_neg_eq_add, ← two_mul, norm_mul]
    norm_num
  rw [hn, hv] at h
  nlinarith

/-- A compact smooth test vanishing on the real axis is linearly bounded by
the distance to that axis. -/
theorem IsTest.bound_by_im_of_zero_axis {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) (hzero : ∀ x : ℝ, ψ (x : ℂ) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |ψ z| ≤ C * |z.im| := by
  obtain ⟨C, hC⟩ := hψ.exists_lipschitzWith
  refine ⟨C, C.2, ?_⟩
  intro z
  have h := hC.dist_le_mul z (z.re : ℂ)
  have hn : ‖z - (z.re : ℂ)‖ = |z.im| := by
    have heq : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [heq]
    simp [norm_mul]
  simpa only [dist_eq_norm, hzero z.re, sub_zero, Real.norm_eq_abs, hn] using h

/-- A linearly vanishing compact smooth test has an actual H¹₀ restriction
to the upper half-plane, with the expected genuine weak gradient. -/
theorem IsTest.upperHalfPlane_indicator_of_bound {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z, |ψ z| ≤ C * |z.im|) :
    MemH10 upperHalfPlane (upperHalfPlane.indicator ψ)
      (upperHalfPlane.indicator (gradient ψ)) := by
  classical
  let K := tsupport ψ
  obtain ⟨η, hη, hηK⟩ := exists_test_eq_one_near_compact isOpen_univ hψ.2.1
    (subset_univ K)
  have hηone {z : Plane} (hz : z ∈ K) : η z = 1 :=
    (hηK.filter_mono (nhds_le_nhdsSet hz)).self_of_nhds
  let b : Plane → ℝ := fun z => C * (η z * η z) * z.im
  have hb : IsTest univ b := by
    have ht := (hη.mul_left hη.1).mul_left Complex.imCLM.contDiff
    convert ht.const_smul C using 1
    funext z
    change C * (η z * η z) * z.im = C * ((η z * η z) * z.im)
    ring
  let B : Plane → ℝ := fun z => max (b z) 0
  have hB := hb.memH10.pos_part
  have hp := ((hψ.mono (subset_univ D)).memH10.pos_part).min hB
  have hm := ((hψ.mono (subset_univ D)).memH10.neg.pos_part).min hB
  let w : Plane → ℝ := fun z => min (max (ψ z) 0) (B z) - min (max (-ψ z) 0) (B z)
  let k : Plane → Plane := fun z =>
    (if max (ψ z) 0 ≤ B z then (if 0 < ψ z then gradient ψ z else 0)
      else (if 0 < b z then gradient b z else 0)) -
    (if max (-ψ z) 0 ≤ B z then (if 0 < -ψ z then -gradient ψ z else 0)
      else (if 0 < b z then gradient b z else 0))
  have hw : MemH10 univ w k := hp.sub hm
  have hvalue : w = upperHalfPlane.indicator ψ := by
    funext z
    dsimp [w]
    by_cases hz : 0 < z.im
    · rw [indicator_of_mem (show z ∈ upperHalfPlane from hz)]
      by_cases hpz : ψ z = 0
      · simp [hpz, B]
      · have hzK : z ∈ K := subset_tsupport ψ hpz
        have hBz : B z = C * z.im := by
          dsimp [B, b]
          rw [hηone hzK]
          simp only [one_mul, mul_one]
          exact max_eq_left (mul_nonneg hC hz.le)
        have hψle : max (ψ z) 0 ≤ C * z.im := by
          apply max_le
          · exact (le_abs_self _).trans (by simpa [abs_of_pos hz] using hbound z)
          · exact mul_nonneg hC hz.le
        have hnegψle : max (-ψ z) 0 ≤ C * z.im := by
          apply max_le
          · exact (neg_le_abs _).trans (by simpa [abs_of_pos hz] using hbound z)
          · exact mul_nonneg hC hz.le
        rw [hBz, min_eq_left hψle, min_eq_left hnegψle]
        exact max_zero_sub_max_neg_zero_eq_self _
    · rw [indicator_of_not_mem (show z ∉ upperHalfPlane from hz)]
      have hbz : b z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hC (mul_self_nonneg _)) (le_of_not_gt hz)
      simp [B, max_eq_right hbz, le_max_right]
  have hgrad : k =ᵐ[volume] upperHalfPlane.indicator (gradient ψ) := by
    have heq := hw.gradient_ae_eq_on_equal ((hψ.mono (subset_univ D)).memH10)
    have hzero := hw.gradient_ae_zero_on_zero
    filter_upwards [heq, hzero] with z hz hz0
    by_cases hzU : z ∈ upperHalfPlane
    · rw [indicator_of_mem hzU]
      apply hz
      rw [hvalue, indicator_of_mem hzU]
    · rw [indicator_of_not_mem hzU]
      apply hz0
      rw [hvalue, indicator_of_not_mem hzU]
  have hw' : MemH10 univ (upperHalfPlane.indicator ψ)
      (upperHalfPlane.indicator (gradient ψ)) :=
    hw.congr (ae_of_all _ fun z => congrFun hvalue z) hgrad
  apply hw'.upperHalfPlane_of_compact_support hψ.2.1
  · exact ae_of_all _ fun z hz => by
      by_cases hzU : z ∈ upperHalfPlane
      · rw [indicator_of_mem hzU, image_eq_zero_of_nmem_tsupport hz]
      · exact indicator_of_not_mem hzU _
  · exact ae_of_all _ fun z hz => indicator_of_not_mem (by
      change ¬ 0 < z.im
      linarith) _

/-- Antisymmetric tests may cross the flat diameter before restriction. No
extra zero-trace or density hypothesis is required for their restriction. -/
theorem IsTest.upperHalfPlane_indicator {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) (hodd : ∀ z, ψ (star z) = -ψ z) :
    MemH10 upperHalfPlane (upperHalfPlane.indicator ψ)
      (upperHalfPlane.indicator (gradient ψ)) := by
  obtain ⟨C, hC, hbound⟩ := hψ.bound_by_im_of_antisymmetric hodd
  exact hψ.upperHalfPlane_indicator_of_bound hC hbound

/-- The same zero-boundary admission holds for any compact smooth function
vanishing on the diameter, including the quadratic Poisson correction. -/
theorem IsTest.upperHalfPlane_indicator_of_zero_axis {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) (hzero : ∀ x : ℝ, ψ (x : ℂ) = 0) :
    MemH10 upperHalfPlane (upperHalfPlane.indicator ψ)
      (upperHalfPlane.indicator (gradient ψ)) := by
  obtain ⟨C, hC, hbound⟩ := hψ.bound_by_im_of_zero_axis hzero
  exact hψ.upperHalfPlane_indicator_of_bound hC hbound

end Torsion

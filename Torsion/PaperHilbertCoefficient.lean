module

public import Torsion.CauchySpectralIdentity

@[expose] public section

/-! # The endpoint integral for the Hilbert coefficient -/

noncomputable section
open Set MeasureTheory
open scoped NNReal Topology

namespace Torsion.Spectral

/-- Where the profile vanishes, symmetric subtraction in the real Hilbert
trace reduces to integration of the original kernel over the support. -/
theorem realCauchyBoundaryRe_at_zeroOfProfile {φ : ℝ → ℝ} {x : ℝ}
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) (hx : φ x = 0) :
    realCauchyBoundaryRe φ x = Real.pi⁻¹ * ∫ s in Icc (-1 : ℝ) 1, φ s / (s - x) := by
  rw [realCauchyBoundaryRe, subtractedRealCauchy_real, hx]
  simp only [sub_zero]
  congr 1
  have hlarge : (∫ t in Icc (-(|x| + 2)) (|x| + 2), φ (x + t) / t) =
      ∫ t : ℝ, φ (x + t) / t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hs : 1 ≤ |x + t| := by
      by_contra! h
      obtain ⟨hl, hu⟩ := abs_lt.mp h
      exact ht ⟨by linarith [le_abs_self x], by linarith [neg_le_abs x]⟩
    simp [hzero _ hs]
  have hsmall : (∫ s in Icc (-1 : ℝ) 1, φ s / (s - x)) = ∫ s : ℝ, φ s / (s - x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    have habs : 1 ≤ |s| := by
      by_contra! h
      exact hs (abs_le.mp h.le)
    simp [hzero _ habs]
  rw [hlarge, hsmall]
  simpa only [add_sub_cancel_left] using
    (integral_add_left_eq_self (μ := volume) (fun s : ℝ => φ s / (s - x)) x)

/-- Fold an integrable function on the symmetric interval onto its positive half. -/
theorem pair_integrable_interval {k : ℝ → ℝ} (hk : IntegrableOn k (Icc (-1 : ℝ) 1)) :
    (∫ s in Icc (-1 : ℝ) 1, k s) = (∫ s in (0 : ℝ)..1, k s + k (-s)) := by
  have hleft : IntervalIntegrable k volume (-1) 0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2
      (hk.mono_set (Icc_subset_Icc_right (by norm_num)))
  have hright : IntervalIntegrable k volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2
      (hk.mono_set (Icc_subset_Icc_left (by norm_num)))
  have hmirror : IntervalIntegrable (fun s : ℝ => k (-s)) volume 0 1 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa only [neg_zero, neg_neg] using hleft.symm
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    intervalIntegral.integral_add hright hmirror, intervalIntegral.integral_comp_neg, neg_zero,
    add_comm]

/-- Formula (2.6) for the linear Hilbert coefficient. The endpoint integrability
hypothesis is the ordinary absolute integrability established by the spectral
endpoint bound. The value of the unbounded kernel at the singleton is immaterial. -/
theorem boundaryConstant_endpoint_integral {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα : 0 < α) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ t ∈ Ioo (-1 : ℝ) 1, realCauchyBoundaryRe φ t = a * height φ t - b)
    (hi : IntegrableOn (fun s : ℝ => φ s / (1 - s)) (Icc (-1 : ℝ) 1)) :
    b = 2 / Real.pi * ∫ s in (0 : ℝ)..1, s * φ s / (1 - s ^ 2) := by
  have he := cauchyDerivativeExtension_re_eq_boundaryVelocity hφ hα hzero hlinear 1
    (by constructor <;> norm_num)
  have htrace : -realCauchyBoundaryRe φ 1 = b := by
    rw [cauchyDerivativeExtension_ofReal] at he
    simpa [boundaryVelocity,
      height_zero_of_one_le_abs φ (by norm_num : 1 ≤ |(1 : ℝ)|)] using he
  rw [realCauchyBoundaryRe_at_zeroOfProfile hzero (hzero 1 (by norm_num))] at htrace
  have hflip (s : ℝ) : φ s / (s - 1) = -(φ s / (1 - s)) := by
    rw [show s - 1 = -(1 - s) by ring, div_neg]
  simp_rw [hflip] at htrace
  rw [integral_neg, mul_neg, neg_neg, pair_integrable_interval hi] at htrace
  have hpair : (∫ s in (0 : ℝ)..1, φ s / (1 - s) + φ (-s) / (1 - -s)) =
      ∫ s in (0 : ℝ)..1, 2 * (s * φ s / (1 - s ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    dsimp only
    rw [hodd s]
    by_cases h1 : s = 1
    · simp [h1, hzero 1 (by norm_num)]
    have hminus : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have hplus : 1 + s ≠ 0 := by linarith [hs'.1]
    rw [sub_neg_eq_add, show 1 - s ^ 2 = (1 - s) * (1 + s) by ring]
    field_simp [hminus, hplus]
    ring
  rw [hpair, intervalIntegral.integral_const_mul] at htrace
  rw [← htrace]
  ring

/-- The analogous integral at the center of the arc. The Hölder estimate
controls division by the parameter at zero. -/
theorem boundaryConstant_center_integral {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα : 0 < α) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ t ∈ Ioo (-1 : ℝ) 1, realCauchyBoundaryRe φ t = a * height φ t - b) :
    a * height φ 0 - b = 2 / Real.pi * ∫ s in (0 : ℝ)..1, φ s / s := by
  have h0 : φ 0 = 0 := by
    have h := hodd 0
    rw [neg_zero] at h
    linarith
  have hi : IntegrableOn (fun s : ℝ => φ s / s) (Icc (-1 : ℝ) 1) := by
    apply (subtractedRealCauchy_integrable hφ hα (by norm_num : (0 : ℝ) ≤ 1) 0).congr_fun
      _ measurableSet_Icc
    intro s _
    simp only [Complex.zero_im, Complex.zero_re, zero_pow (by norm_num : 2 ≠ 0),
      add_zero, zero_add, h0, sub_zero]
    by_cases hs : s = 0
    · simp [hs]
    · field_simp
  have he := hlinear 0 (by constructor <;> norm_num)
  rw [realCauchyBoundaryRe_at_zeroOfProfile hzero h0] at he
  simp only [sub_zero] at he
  rw [pair_integrable_interval hi] at he
  have hpair (s : ℝ) : φ s / s + φ (-s) / (-s) = 2 * (φ s / s) := by
    rw [hodd s, neg_div_neg_eq, two_mul]
  simp_rw [hpair] at he
  rw [intervalIntegral.integral_const_mul] at he
  rw [← he]
  ring

/-- The half-width of the flat boundary segment, in the normalization
of the unscaled conformal map. -/
theorem cauchyEndpoint_halfWidth_integral (φ : ℝ → ℝ) :
    -(cauchyExtension φ (1 : ℂ)).re = Real.pi⁻¹ *
      ∫ s in Icc (-1 : ℝ) 1, height φ s / (1 - s) := by
  have hY (s : ℝ) (hs : 1 ≤ |s|) := height_zero_of_one_le_abs φ hs
  have h := cauchyExtension_ofReal φ (1 : ℝ)
  rw [hY 1 (by norm_num), realCauchyBoundaryRe_at_zeroOfProfile hY (hY 1 (by norm_num))] at h
  have hre := congrArg Complex.re h
  simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_re] at hre
  rw [hre]
  have hflip (s : ℝ) : height φ s / (s - 1) = -(height φ s / (1 - s)) := by
    rw [show s - 1 = -(1 - s) by ring, div_neg]
  simp_rw [hflip]
  rw [integral_neg, mul_neg, neg_neg]

end Torsion.Spectral

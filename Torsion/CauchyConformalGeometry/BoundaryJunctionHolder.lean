import Torsion.CauchyConformalGeometry.BoundaryHolder
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Genuine C¹,α charts through the free-arc junctions

Integrate the actual free-arc tangent after clamping its parameter to the
closed free interval. The resulting chart is the actual Cauchy boundary
on that interval and continues linearly along the flat side at both ends.
Its derivative is globally Hölder with the original profile exponent.
This concerns the physical boundary chart, whose choice of speed on the
flat side is independent of the original Cauchy real parameter.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The actual closed-free-arc tangent, held constant beyond its endpoints. -/
def cauchyJoinedTangent (φ : ℝ → ℝ) (t : ℝ) : ℂ :=
  cauchyDerivativeExtension φ
    (((projIcc (-1 : ℝ) 1 (by norm_num) t : Icc (-1 : ℝ) 1) : ℝ) : ℂ)

/-- A concrete physical boundary chart: the actual free arc with linear
continuations along the flat side at its two junctions. -/
def cauchyJoinedBoundary (φ : ℝ → ℝ) (t : ℝ) : ℂ :=
  cauchyExtension φ (0 : ℂ) + ∫ s in (0 : ℝ)..t, cauchyJoinedTangent φ s

/-- Clamping does not change the actual free-arc tangent. -/
theorem cauchyJoinedTangent_eq_on_interval {φ : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    cauchyJoinedTangent φ t = cauchyDerivativeExtension φ (t : ℂ) := by
  unfold cauchyJoinedTangent
  rw [projIcc_of_mem (show (-1 : ℝ) ≤ 1 by norm_num) ht]

/-- Continuity of the genuine derivative extension proves continuity of
the clamped tangent, including both physical junctions. -/
theorem cauchyJoinedTangent_continuous {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) : Continuous (cauchyJoinedTangent φ) := by
  exact (cauchyDerivativeExtension_boundary_continuous hφ hα0 hzero).comp
    (continuous_subtype_val.comp continuous_projIcc)

/-- The primitive construction gives the actual derivative of the joined
chart everywhere, including the two join parameters. -/
theorem cauchyJoinedBoundary_hasDerivAt {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) (t : ℝ) :
    HasDerivAt (cauchyJoinedBoundary φ) (cauchyJoinedTangent φ t) t := by
  have hc := cauchyJoinedTangent_continuous hφ hα0 hzero
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

/-- The joined chart really coincides with the original actual boundary
parametrization on the whole free arc. -/
theorem cauchyJoinedBoundary_eq_on_interval {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    cauchyJoinedBoundary φ t = cauchyExtension φ (t : ℂ) := by
  have hint : IntervalIntegrable (fun s : ℝ => cauchyDerivativeExtension φ (s : ℂ)) volume 0 t :=
    (cauchyDerivativeExtension_boundary_continuous hφ hα0 hzero).intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ uIcc (0 : ℝ) t) => cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero s) hint
  have heq : (∫ s in (0 : ℝ)..t, cauchyJoinedTangent φ s) =
      ∫ s in (0 : ℝ)..t, cauchyDerivativeExtension φ (s : ℂ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact cauchyJoinedTangent_eq_on_interval
      (uIcc_subset_Icc (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) ht hs)
  rw [cauchyJoinedBoundary, heq, hFTC]
  simp

/-- The joined tangent equals the positive-real endpoint tangent on the
entire right continuation. -/
theorem cauchyJoinedTangent_eq_right {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : 1 ≤ t) : cauchyJoinedTangent φ t = (b : ℂ) := by
  rw [cauchyJoinedTangent, projIcc_of_right_le _ ht]
  change cauchyDerivativeExtension φ ((1 : ℝ) : ℂ) = (b : ℂ)
  rw [cauchy_boundary_tangent_eq hφ hα0 hzero hlinear (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1),
    hzero 1 (by norm_num)]
  simp [boundaryVelocity, height_zero_of_one_le_abs φ (by norm_num : (1 : ℝ) ≤ |1|)]

/-- The same actual endpoint tangent is held constant to the left. -/
theorem cauchyJoinedTangent_eq_left {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ≤ -1) : cauchyJoinedTangent φ t = (b : ℂ) := by
  rw [cauchyJoinedTangent, projIcc_of_le_left _ ht]
  change cauchyDerivativeExtension φ ((-1 : ℝ) : ℂ) = (b : ℂ)
  rw [cauchy_boundary_tangent_eq hφ hα0 hzero hlinear (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1),
    hzero (-1) (by norm_num)]
  simp [boundaryVelocity, height_zero_of_one_le_abs φ (by norm_num : (1 : ℝ) ≤ |(-1 : ℝ)|)]

private theorem cauchyJoinedBoundary_sub {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) (t s : ℝ) :
    cauchyJoinedBoundary φ t - cauchyJoinedBoundary φ s =
      ∫ r in s..t, cauchyJoinedTangent φ r := by
  have hc := cauchyJoinedTangent_continuous hφ hα0 hzero
  simpa only [cauchyJoinedBoundary, add_sub_add_left_eq_sub] using
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 t) (hc.intervalIntegrable 0 s)

/-- The right continuation is an explicit straight parametrization of the
physical flat side adjacent to its junction. -/
theorem cauchyJoinedBoundary_eq_right {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : 1 ≤ t) :
    cauchyJoinedBoundary φ t = cauchyExtension φ (1 : ℂ) + ((b * (t - 1) : ℝ) : ℂ) := by
  have hsub := cauchyJoinedBoundary_sub hφ hα0 hzero t 1
  have hi : (∫ r in (1 : ℝ)..t, cauchyJoinedTangent φ r) = ((b * (t - 1) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_congr (g := fun _ => (b : ℂ)) (fun r hr =>
      cauchyJoinedTangent_eq_right hφ hα0 hzero hlinear
        (by simpa only [min_eq_left ht] using hr.1)), intervalIntegral.integral_const]
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring
  rw [hi, cauchyJoinedBoundary_eq_on_interval hφ hα0 hα1 hodd hzero (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1)] at hsub
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one] at hsub
  linear_combination hsub

/-- The analogous explicit straight continuation at the left junction. -/
theorem cauchyJoinedBoundary_eq_left {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ≤ -1) :
    cauchyJoinedBoundary φ t = cauchyExtension φ (-1 : ℂ) + ((b * (t + 1) : ℝ) : ℂ) := by
  have hsub := cauchyJoinedBoundary_sub hφ hα0 hzero t (-1)
  have hi : (∫ r in (-1 : ℝ)..t, cauchyJoinedTangent φ r) = ((b * (t + 1) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_congr (g := fun _ => (b : ℂ)) (fun r hr =>
      cauchyJoinedTangent_eq_left hφ hα0 hzero hlinear
        (by simpa only [max_eq_left ht] using hr.2)), intervalIntegral.integral_const]
    simp only [Complex.real_smul, Complex.ofReal_mul]
    push_cast
    ring
  rw [hi, cauchyJoinedBoundary_eq_on_interval hφ hα0 hα1 hodd hzero (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1)] at hsub
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one] at hsub
  linear_combination hsub

/-- The physical continuation has a globally Hölder tangent because clamp
is 1-Lipschitz and the actual closed free-arc tangent is Hölder. -/
theorem cauchyJoinedTangent_holder {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    ∃ K : ℝ≥0, HolderWith K α (cauchyJoinedTangent φ) := by
  obtain ⟨K, hK⟩ := cauchy_boundary_tangent_holderOn hφ hα0 hα1 hodd hzero hlinear
  refine ⟨K, ?_⟩
  have h := hK.holderWith.comp
    ((LipschitzWith.projIcc (show (-1 : ℝ) ≤ 1 by norm_num)).holderWith)
  simpa only [NNReal.one_rpow, mul_one, Function.comp_def, Set.restrict,
    cauchyJoinedTangent] using h

/-- Genuine C¹ regularity of the physical chart through both joins. -/
theorem cauchyJoinedBoundary_contDiff_one {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) :
    ContDiff ℝ 1 (cauchyJoinedBoundary φ) := by
  apply contDiff_one_iff_deriv.2
  refine ⟨fun t => (cauchyJoinedBoundary_hasDerivAt hφ hα0 hzero t).differentiableAt, ?_⟩
  have heq : deriv (cauchyJoinedBoundary φ) = cauchyJoinedTangent φ :=
    funext fun t => (cauchyJoinedBoundary_hasDerivAt hφ hα0 hzero t).deriv
  rw [heq]
  exact cauchyJoinedTangent_continuous hφ hα0 hzero

/-- The actual derivative of the physical chart is globally α-Hölder. -/
theorem cauchyJoinedBoundary_deriv_holder {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    ∃ K : ℝ≥0, HolderWith K α (deriv (cauchyJoinedBoundary φ)) := by
  have heq : deriv (cauchyJoinedBoundary φ) = cauchyJoinedTangent φ :=
    funext fun t => (cauchyJoinedBoundary_hasDerivAt hφ hα0 hzero t).deriv
  rw [heq]
  exact cauchyJoinedTangent_holder hφ hα0 hα1 hodd hzero hlinear

/-- The physical boundary chart is regular everywhere, including both
junctions, by nonvanishing of the actual closed free-arc tangent. -/
theorem cauchyJoinedBoundary_deriv_ne_zero {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) (t : ℝ) :
    deriv (cauchyJoinedBoundary φ) t ≠ 0 := by
  rw [(cauchyJoinedBoundary_hasDerivAt hφ hα0 hzero t).deriv]
  exact cauchyDerivativeExtension_ne_zero_on_interval ha hφ hα0 hα1 hodd hzero hpos hlinear
    (projIcc (-1 : ℝ) 1 (by norm_num) t).property

end Torsion.Spectral

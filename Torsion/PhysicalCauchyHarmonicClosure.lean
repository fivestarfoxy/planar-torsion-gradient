import Torsion.PhysicalCauchyHarmonicLp

/-!
# Constructed continuous closed-image boundary lift

The actual Poisson integral extends continuously to the one-point
compactified closed half-plane, with zero at infinity. Composition with the
proved actual closed-image homeomorphism constructs a genuine continuous
function on the whole physical domain closure, including every free/flat
junction and the marked origin.
-/

noncomputable section
open Set Filter MeasureTheory Bornology Metric
open scoped Topology NNReal OnePoint

namespace Torsion.Spectral

def compactifiedPoissonLift (g : ℝ → ℝ) (z : OnePoint CauchyClosedHalfPlane) : ℝ :=
  z.elim 0 (fun w : CauchyClosedHalfPlane => poissonExtension g (w : Plane))

theorem poisson_closedHalfPlane_tendsto_zero {g : ℝ → ℝ}
    (hg : Continuous g) (hgzero : ∀ x : ℝ, 1 ≤ |x| → g x = 0) :
    Tendsto (fun z : CauchyClosedHalfPlane => poissonExtension g (z : Plane))
      (coclosedCompact CauchyClosedHalfPlane) (𝓝 0) := by
  have hs : IsClosed {z : Plane | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have hsub : Tendsto (fun z : CauchyClosedHalfPlane => (z : Plane))
      (coclosedCompact CauchyClosedHalfPlane) (cocompact Plane) := by
    simpa only [coclosedCompact_eq_cocompact] using hs.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have hn : Tendsto (fun z : CauchyClosedHalfPlane => ‖(z : Plane)‖)
      (coclosedCompact CauchyClosedHalfPlane) atTop := tendsto_norm_cocompact_atTop.comp hsub
  have hC : Tendsto (fun z : CauchyClosedHalfPlane => realCauchy g (z : Plane))
      (coclosedCompact CauchyClosedHalfPlane) (𝓝 0) := by
    have h := (cauchy_integral_tendsto_zero (Complex.continuous_ofReal.comp hg).continuousOn hn).const_mul
      (-((Real.pi : Plane)⁻¹))
    simpa only [Function.comp_apply, realCauchy, mul_zero] using h
  have hCn : Tendsto (fun z : CauchyClosedHalfPlane => ‖realCauchy g (z : Plane)‖)
      (coclosedCompact CauchyClosedHalfPlane) (𝓝 0) := by simpa only [norm_zero] using hC.norm
  apply squeeze_zero_norm' _ hCn
  filter_upwards [hn.eventually (eventually_gt_atTop (1 : ℝ))] with z hzn
  by_cases him : (z : Plane).im = 0
  · have hzreal : ((z : Plane).re : Plane) = (z : Plane) := by apply Complex.ext <;> simp [him]
    have hnorm : 1 ≤ |(z : Plane).re| := by
      have hh : 1 < ‖((z : Plane).re : Plane)‖ := by rw [hzreal]; exact hzn
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hh.le
    rw [← hzreal, poissonExtension_ofReal, hgzero _ hnorm, norm_zero]
    exact norm_nonneg _
  · have hzH : (z : Plane) ∈ upperHalfPlane := lt_of_le_of_ne z.property (Ne.symm him)
    rw [← realCauchy_im_eq_poissonExtension hg hgzero hzH, Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _

theorem compactifiedPoissonLift_continuous {g : ℝ → ℝ}
    (hg : Continuous g) (hgzero : ∀ x : ℝ, 1 ≤ |x| → g x = 0) :
    Continuous (compactifiedPoissonLift g) := by
  apply (OnePoint.continuous_iff _).mpr
  exact ⟨poisson_closedHalfPlane_tendsto_zero hg hgzero,
    (poissonExtension_continuous hg hgzero).comp continuous_subtype_val⟩

/-- A genuine continuous physical boundary extension of the actual harmonic
lift, with the prescribed finite parameter data and zero marked value. -/
theorem exists_continuous_physicalHarmonicLift_closure
    {φ g : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hg : Continuous g) (hgzero : ∀ x : ℝ, 1 ≤ |x| → g x = 0) :
    ∃ H : C(closure (cauchyImage φ), ℝ),
      (∀ w (hw : w ∈ cauchyImage φ), H ⟨w, subset_closure hw⟩ = physicalHarmonicLift φ g w) ∧
      (∀ h0 : (0 : Plane) ∈ closure (cauchyImage φ), H ⟨0, h0⟩ = 0) ∧
      (∀ t : ℝ, ∀ ht : cauchyExtension φ (t : Plane) ∈ closure (cauchyImage φ),
        H ⟨cauchyExtension φ (t : Plane), ht⟩ = g t) := by
  let e := cauchyClosureHomeomorph hφ hα0 hα1 hodd hzero hpos
  let H : C(closure (cauchyImage φ), ℝ) :=
    ⟨fun w => compactifiedPoissonLift g (e.symm w),
      (compactifiedPoissonLift_continuous hg hgzero).comp e.symm.continuous⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro w hw
    let z : CauchyClosedHalfPlane := ⟨cauchyInverse φ w, (cauchyInverse_mem hw).le⟩
    have heq : e (z : OnePoint CauchyClosedHalfPlane) = ⟨w, subset_closure hw⟩ := by
      apply Subtype.ext
      change cauchyExtension φ (cauchyInverse φ w) = w
      rw [cauchyExtension_eq (hφ.continuous hα0).continuousOn (cauchyInverse_mem hw)]
      exact cauchy_cauchyInverse hw
    change compactifiedPoissonLift g (e.symm ⟨w, subset_closure hw⟩) = _
    rw [← heq, e.symm_apply_apply]
    exact (realCauchy_im_eq_poissonExtension hg hgzero (cauchyInverse_mem hw)).symm
  · intro h0
    have heq : e (∞ : OnePoint CauchyClosedHalfPlane) = ⟨0, h0⟩ := by
      apply Subtype.ext
      rfl
    change compactifiedPoissonLift g (e.symm ⟨0, h0⟩) = 0
    rw [← heq, e.symm_apply_apply]
    rfl
  · intro t ht
    let z : CauchyClosedHalfPlane := ⟨(t : Plane), by simp⟩
    have heq : e (z : OnePoint CauchyClosedHalfPlane) = ⟨cauchyExtension φ (t : Plane), ht⟩ := by
      apply Subtype.ext
      rfl
    change compactifiedPoissonLift g (e.symm ⟨cauchyExtension φ (t : Plane), ht⟩) = g t
    rw [← heq, e.symm_apply_apply]
    exact poissonExtension_ofReal g t

end Torsion.Spectral

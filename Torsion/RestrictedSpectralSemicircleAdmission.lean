import Torsion.RestrictedSpectralSemicircle
import Torsion.RestrictedSpectralSemicircleWeight
import Torsion.RestrictedSpectralSemicircleKernel
import Torsion.RestrictedSpectralGagliardoKernel

/-!
# Actual restricted form admission of the semicircle barrier

An integrable product majorant controls its genuine two-point difference
kernel. Flat value truncations then give actual core approximants with
bounded original Fourier energy, so the existing weak closure theorem
admits this endpoint-square-root profile to the original form domain.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

private theorem semicircleKernelWeight_kernel_bound {x y : ℝ}
    (hx : 1 - x ^ 2 ≠ 0) (hy : 1 - y ^ 2 ≠ 0) :
    (semicircleBarrier y - semicircleBarrier x) ^ 2 / (y - x) ^ 2 ≤
      16 * semicircleKernelWeight x * semicircleKernelWeight y := by
  by_cases hxsmall : |x| < 2
  · by_cases hysmall : |y| < 2
    · simpa only [semicircleBarrier, semicircleKernelWeight, if_pos hxsmall, if_pos hysmall]
        using semicircleKernel_local_bound hxsmall hysmall hx hy
    · simpa only [semicircleBarrier, semicircleKernelWeight, if_pos hxsmall, if_neg hysmall]
        using semicircleKernel_tail_bound hx (le_of_not_gt hysmall)
  · by_cases hysmall : |y| < 2
    · have h := semicircleKernel_tail_bound hy (le_of_not_gt hxsmall)
      have heq : (semicircleBarrier y - semicircleBarrier x) ^ 2 / (y - x) ^ 2 =
          (semicircleBarrier x - semicircleBarrier y) ^ 2 / (x - y) ^ 2 := by
        rw [← neg_sub (semicircleBarrier x) (semicircleBarrier y), neg_sq,
          ← neg_sub x y, neg_sq]
      rw [heq]
      simpa only [semicircleBarrier, semicircleKernelWeight, if_neg hxsmall, if_pos hysmall,
        mul_assoc, mul_comm, mul_left_comm] using h
    · have hx0 := semicircleBarrier_zero_exterior x (by linarith [le_of_not_gt hxsmall])
      have hy0 := semicircleBarrier_zero_exterior y (by linarith [le_of_not_gt hysmall])
      rw [hx0, hy0, sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_div]
      exact mul_nonneg (mul_nonneg (by norm_num) (semicircleKernelWeight_nonneg x))
        (semicircleKernelWeight_nonneg y)

private theorem ae_not_semicircle_endpoint : ∀ᵐ x : ℝ ∂volume, 1 - x ^ 2 ≠ 0 := by
  have h₁ : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
    simpa only [mem_singleton_iff] using (Set.countable_singleton (1 : ℝ)).ae_not_mem volume
  have h₂ : ∀ᵐ x : ℝ ∂volume, x ≠ -1 := by
    simpa only [mem_singleton_iff] using (Set.countable_singleton (-1 : ℝ)).ae_not_mem volume
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  intro h
  have : x = 1 ∨ x = -1 := by
    have hh : x ^ 2 = 1 := by linarith
    exact (sq_eq_one_iff).1 hh
  exact this.elim hx₁ hx₂

/-- The actual two-point difference kernel of the square-root profile is
integrable across the endpoint singularities and along the infinite tails. -/
theorem semicircleBarrier_gagliardoKernel_integrable :
    Integrable (fun p : ℝ × ℝ =>
      (semicircleBarrier p.2 - semicircleBarrier p.1) ^ 2 / (p.2 - p.1) ^ 2)
      (volume : Measure (ℝ × ℝ)) := by
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      16 * semicircleKernelWeight p.1 * semicircleKernelWeight p.2)
      (volume : Measure (ℝ × ℝ)) := by
    convert (semicircleKernelWeight_integrable.mul_prod
      semicircleKernelWeight_integrable).const_mul (16 : ℝ) using 1
    funext p
    ring
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (semicircleBarrier p.2 - semicircleBarrier p.1) ^ 2 / (p.2 - p.1) ^ 2)
      (volume : Measure (ℝ × ℝ)) := by
    apply Measurable.aestronglyMeasurable
    exact (((semicircleBarrier_continuous.measurable.comp measurable_snd).sub
      (semicircleBarrier_continuous.measurable.comp measurable_fst)).pow_const 2).div
      ((measurable_snd.sub measurable_fst).pow_const 2)
  apply hmajor.mono' hm
  have hx := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).ae ae_not_semicircle_endpoint
  have hy := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).ae ae_not_semicircle_endpoint
  filter_upwards [hx, hy] with p hp₁ hp₂
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact semicircleKernelWeight_kernel_bound hp₁ hp₂

/-- The genuine nonnegative difference energy of the semicircle is finite. -/
theorem semicircleBarrier_gagliardoEnergy_ne_top : gagliardoEnergy semicircleBarrier ≠ ∞ := by
  rw [gagliardoEnergy_eq_double semicircleBarrier_continuous.measurable]
  rw [← lintegral_prod _ (measurable_gagliardoKernel
    semicircleBarrier_continuous.measurable).aemeasurable]
  exact (lintegral_ofReal_ne_top_iff_integrable
    semicircleBarrier_gagliardoKernel_integrable.aestronglyMeasurable
    (ae_of_all _ fun p => div_nonneg (sq_nonneg _) (sq_nonneg _))).2
      semicircleBarrier_gagliardoKernel_integrable

/-- The actual zero-exterior semicircle belongs to the original restricted
Fourier form domain; no endpoint regularity or spectral premise is assumed. -/
theorem semicircleBarrier_memRestrictedFormDomain : MemRestrictedFormDomain semicircleBarrier := by
  apply (memRestrictedFormDomain_of_nonnegative_gagliardo semicircleBarrier_continuous
    semicircleBarrier_contDiffOn ?_ semicircleBarrier_nonneg
    semicircleBarrier_gagliardoEnergy_ne_top).1
  intro x hx
  exact semicircleBarrier_zero_exterior x (le_of_not_gt (fun h => hx (abs_lt.mp h)))

end Torsion.Spectral

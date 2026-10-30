module

public import Torsion.RestrictedSpectralOddGap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Strict sign of the paired odd nonlocal kernel at a zero minimum

The reflected kernel is strictly smaller on the positive half-line,
except at the single diagonal point. Consequently a nonnegative density
with a non-null positive set gives a strictly negative minimum integral,
whenever that concrete singular integral is integrable. Identification
and integrability of an actual differential operator are separate steps.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- The positive-half paired coefficient in the original odd operator. -/
def oddMinimumCoefficient (x s : ℝ) : ℝ :=
  1 / (x - s) ^ 2 - 1 / (x + s) ^ 2

/-- Off the diagonal both variables positive give a strictly positive
coefficient in the actual paired kernel. -/
theorem oddMinimumCoefficient_pos {x s : ℝ} (hx : 0 < x) (hs : 0 < s) (hne : x ≠ s) :
    0 < oddMinimumCoefficient x s :=
  oddAbsGap_coefficient_pos hx hs hne

/-- The minimum integrand is nonpositive at every nonnegative value,
away from the diagonal. -/
theorem oddMinimumIntegrand_nonpos {f : ℝ → ℝ} {x s : ℝ}
    (hx : 0 < x) (hs : 0 < s) (hne : x ≠ s) (hf : 0 ≤ f s) :
    -f s * oddMinimumCoefficient x s ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hf)
    (oddMinimumCoefficient_pos hx hs hne).le

/-- A positive density value makes the paired minimum integrand strictly
negative away from the diagonal. -/
theorem oddMinimumIntegrand_neg {f : ℝ → ℝ} {x s : ℝ}
    (hx : 0 < x) (hs : 0 < s) (hne : x ≠ s) (hf : 0 < f s) :
    -f s * oddMinimumCoefficient x s < 0 :=
  mul_neg_of_neg_of_pos (neg_neg_of_pos hf) (oddMinimumCoefficient_pos hx hs hne)

/-- The actual singular minimum kernel has a strictly negative integral
for a nonnegative positive-half density with a non-null positive set.
Only integrability of that explicitly displayed kernel is assumed. -/
theorem integral_oddMinimumIntegrand_neg {f : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x)
    (hf : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hpos : volume {s : ℝ | 0 < s ∧ 0 < f s} ≠ 0)
    (hi : IntegrableOn (fun s : ℝ => -f s * oddMinimumCoefficient x s) (Ioi (0 : ℝ))) :
    (∫ s in Ioi (0 : ℝ), -f s * oddMinimumCoefficient x s) < 0 := by
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ x := by
    rw [ae_iff]
    simp
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s : ℝ => f s * oddMinimumCoefficient x s) := by
    filter_upwards [hf, ae_restrict_of_ae hne, ae_restrict_mem measurableSet_Ioi]
      with s hfs hsne hs
    exact mul_nonneg hfs (oddMinimumCoefficient_pos hx hs hsne.symm).le
  have hint : IntegrableOn (fun s : ℝ => f s * oddMinimumCoefficient x s) (Ioi (0 : ℝ)) := by
    change Integrable (fun s : ℝ => f s * oddMinimumCoefficient x s)
      (volume.restrict (Ioi (0 : ℝ)))
    convert Integrable.neg hi using 1
    funext s
    simp only [Pi.neg_apply]
    ring
  have hnotzero : ¬ (fun s : ℝ => f s * oddMinimumCoefficient x s) =ᵐ[
      volume.restrict (Ioi (0 : ℝ))] 0 := by
    intro hz
    have hfzero : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
      filter_upwards [hz, ae_restrict_of_ae hne, ae_restrict_mem measurableSet_Ioi]
        with s hzs hsne hs
      exact (mul_eq_zero.mp hzs).resolve_right (oddMinimumCoefficient_pos hx hs hsne.symm).ne'
    have hnull : ∀ᵐ s : ℝ ∂volume, ¬(0 < s ∧ 0 < f s) := by
      filter_upwards [ae_imp_of_ae_restrict hfzero] with s hs
      intro hp
      have hz : f s = 0 := hs hp.1
      linarith [hp.2]
    apply hpos
    simpa only [ae_iff, not_not] using hnull
  have hpositive : 0 < ∫ s in Ioi (0 : ℝ), f s * oddMinimumCoefficient x s := by
    apply lt_of_le_of_ne (integral_nonneg_of_ae hnonneg)
    intro hz
    exact hnotzero ((integral_eq_zero_iff_of_nonneg_ae hnonneg hint).1 hz.symm)
  simpa only [neg_mul, integral_neg, neg_lt_zero] using hpositive

/-- Formula-expanded version for direct use in the actual weak operator. -/
theorem integral_pairedOddMinimumKernel_neg {f : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hf : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hpos : volume {s : ℝ | 0 < s ∧ 0 < f s} ≠ 0)
    (hi : IntegrableOn (fun s : ℝ => -f s *
      (1 / (x - s) ^ 2 - 1 / (x + s) ^ 2)) (Ioi (0 : ℝ))) :
    (∫ s in Ioi (0 : ℝ), -f s *
      (1 / (x - s) ^ 2 - 1 / (x + s) ^ 2)) < 0 :=
  integral_oddMinimumIntegrand_neg hx hf hpos hi

/-- The original integrable whole-line function splits into its two
positive-half reflected pieces. -/
theorem integral_eq_positive_reflection {F : ℝ → ℝ} (hi : Integrable F) :
    (∫ s : ℝ, F s) = ∫ s in Ioi (0 : ℝ), F s + F (-s) := by
  have hneg : Integrable (fun s : ℝ => F (-s)) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_emb
      (Homeomorph.neg ℝ).measurableEmbedding).2 hi
  rw [integral_add hi.integrableOn hneg.integrableOn]
  have hreflection := integral_comp_neg_Ioi (0 : ℝ) F
  simp only [neg_zero] at hreflection
  rw [hreflection]
  simpa only [compl_Ioi] using (integral_add_compl measurableSet_Ioi hi).symm

/-- For the actual odd density, reflection gives the positive-half paired
kernel and proves its integrability directly from the whole quotient. -/
theorem integral_odd_quotient_sq_eq_positive_pair {f : ℝ → ℝ} {x : ℝ}
    (hodd : Function.Odd f) (hi : Integrable (fun s : ℝ => f s / (x - s) ^ 2)) :
    IntegrableOn (fun s : ℝ => f s * oddMinimumCoefficient x s) (Ioi (0 : ℝ)) ∧
      (∫ s : ℝ, f s / (x - s) ^ 2) =
        ∫ s in Ioi (0 : ℝ), f s * oddMinimumCoefficient x s := by
  let F : ℝ → ℝ := fun s => f s / (x - s) ^ 2
  have hneg : Integrable (fun s : ℝ => F (-s)) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_emb
      (Homeomorph.neg ℝ).measurableEmbedding).2 hi
  have heq : (fun s : ℝ => F s + F (-s)) =
      fun s : ℝ => f s * oddMinimumCoefficient x s := by
    funext s
    dsimp only [F, oddMinimumCoefficient]
    rw [hodd s]
    ring
  constructor
  · rw [← heq]
    exact hi.integrableOn.add hneg.integrableOn
  · rw [integral_eq_positive_reflection hi, heq]

/-- The whole nonlocal quotient is strictly positive at a positive point
for an odd density nonnegative on the positive half with non-null positive
set, provided the explicitly displayed whole quotient is integrable. -/
theorem integral_odd_quotient_sq_pos {f : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hodd : Function.Odd f)
    (hf : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hpos : volume {s : ℝ | 0 < s ∧ 0 < f s} ≠ 0)
    (hi : Integrable (fun s : ℝ => f s / (x - s) ^ 2)) :
    0 < ∫ s : ℝ, f s / (x - s) ^ 2 := by
  obtain ⟨hpair, heq⟩ := integral_odd_quotient_sq_eq_positive_pair hodd hi
  have hint : IntegrableOn (fun s : ℝ => -f s * oddMinimumCoefficient x s) (Ioi (0 : ℝ)) := by
    change Integrable (fun s : ℝ => -f s * oddMinimumCoefficient x s)
      (volume.restrict (Ioi (0 : ℝ)))
    convert Integrable.neg hpair using 1
    funext s
    simp only [Pi.neg_apply]
    ring
  have hnegative := integral_oddMinimumIntegrand_neg hx hf hpos hint
  rw [heq]
  simpa only [neg_mul, integral_neg, neg_lt_zero] using hnegative

end Torsion.Spectral

module

public import Torsion.RestrictedSpectralOddKernelMinimum
public import Torsion.RestrictedSpectralPositiveSets

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The actual exterior residual and its odd kernel signs

The residual is the original density's ordinary compact interval integral.
Its oddness is a change of variables. Actual restricted support and L¹
integrability prove that the whole double-pole quotient is integrable
outside the interval, so the positive-half sign is a theorem of the
concrete kernel. No operator identity or concavity is assumed here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- The actual compactly supported density's exterior residual integral. -/
def exteriorResidual (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ s in Icc (-1 : ℝ) 1, f s / (y - s) ^ 2

theorem exteriorResidual_odd {f : ℝ → ℝ} (hodd : Function.Odd f) :
    Function.Odd (exteriorResidual f) := by
  intro y
  have href := (Homeomorph.neg ℝ).measurableEmbedding.setIntegral_map
    (μ := (volume : Measure ℝ))
    (fun s : ℝ => f s / (-y - s) ^ 2) (Icc (-1 : ℝ) 1)
  change (∫ s in Icc (-1 : ℝ) 1, f s / (-y - s) ^ 2
      ∂Measure.map (fun s : ℝ => -s) volume) =
    ∫ s in (fun s : ℝ => -s) ⁻¹' Icc (-1 : ℝ) 1, f (-s) / (-y - -s) ^ 2 at href
  rw [Measure.map_neg_eq_self] at href
  have hpre : (fun s : ℝ => -s) ⁻¹' Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) 1 := by
    ext s
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hpre] at href
  have heq : (fun s : ℝ => f (-s) / (-y - -s) ^ 2) =
      fun s : ℝ => -(f s / (y - s) ^ 2) := by
    funext s
    rw [hodd s]
    have hd : (-y - -s) ^ 2 = (y - s) ^ 2 := by ring
    rw [hd, neg_div]
  rw [heq, integral_neg] at href
  unfold exteriorResidual
  rw [href]
  ring

/-- Actual restricted support makes the full double-pole quotient
integrable at every exterior point, with a uniform positive denominator. -/
theorem MemRestrictedFormDomain.integrable_div_sq_exterior {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) {y : ℝ} (hy : 1 < |y|) :
    Integrable (fun s : ℝ => f s / (y - s) ^ 2) := by
  have hδ : 0 < |y| - 1 := by linarith
  have hm : AEStronglyMeasurable (fun s : ℝ => f s / (y - s) ^ 2) volume := by
    simpa only [div_eq_mul_inv] using hf.integrable.aestronglyMeasurable.mul
      (((continuous_const.sub continuous_id).pow 2).measurable.inv.aestronglyMeasurable)
  apply (hf.integrable.norm.div_const ((|y| - 1) ^ 2)).mono' hm
  filter_upwards [hf.2.2.1] with s hs
  by_cases hsi : s ∈ Icc (-1 : ℝ) 1
  · have hsa : |s| ≤ 1 := abs_le.2 hsi
    have hd : |y| - 1 ≤ |y - s| := by linarith [abs_sub_abs_le_abs_sub y s]
    rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hδ)
    exact pow_le_pow_left₀ hδ.le hd 2
  · have hnot : s ∉ Ioo (-1 : ℝ) 1 := fun h => hsi ⟨h.1.le, h.2.le⟩
    rw [hs hnot]
    simp

/-- The original compact interval formula agrees with the whole quotient
for every actual restricted form member. -/
theorem MemRestrictedFormDomain.exteriorResidual_eq_whole {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (y : ℝ) :
    exteriorResidual f y = (1 / Real.pi) * ∫ s : ℝ, f s / (y - s) ^ 2 := by
  unfold exteriorResidual
  congr 1
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [hf.2.2.1] with s hs hnot
  have hsi : s ∉ Ioo (-1 : ℝ) 1 := fun h => hnot ⟨h.1.le, h.2.le⟩
  simp [hs hsi]

/-- An actual nonzero odd restricted form member with nonnegative
positive half has a strictly positive residual on the right exterior. -/
theorem MemRestrictedFormDomain.exteriorResidual_pos {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f)
    (hne : ¬ f =ᵐ[volume] 0) (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    {y : ℝ} (hy : 1 < y) : 0 < exteriorResidual f y := by
  have hset := hf.positive_half_set_measure_ne_zero hodd hne hnonneg
  have hpos : volume {s : ℝ | 0 < s ∧ 0 < f s} ≠ 0 := by
    intro hz
    apply hset
    have hsub : {s : ℝ | s ∈ Ioo (0 : ℝ) 1 ∧ 0 < f s} ⊆
        {s : ℝ | 0 < s ∧ 0 < f s} := fun s hs => ⟨hs.1.1, hs.2⟩
    exact measure_mono_null hsub hz
  rw [hf.exteriorResidual_eq_whole y]
  apply mul_pos (one_div_pos.2 Real.pi_pos)
  exact integral_odd_quotient_sq_pos (by linarith) hodd hnonneg hpos
    (hf.integrable_div_sq_exterior (hy.trans_le (le_abs_self y)))

theorem IsRestrictedEigenfunction.exteriorResidual_pos {f : ℝ → ℝ} {a : ℝ}
    (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    {y : ℝ} (hy : 1 < y) : 0 < exteriorResidual f y :=
  hf.1.exteriorResidual_pos hodd hf.2.1 hnonneg hy

/-- The exterior residual, extended by zero on the closed source interval. -/
def exteriorResidualZero (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  if 1 < |y| then exteriorResidual f y else 0

theorem exteriorResidualZero_odd {f : ℝ → ℝ} (hodd : Function.Odd f) :
    Function.Odd (exteriorResidualZero f) := by
  intro y
  simp only [exteriorResidualZero, abs_neg]
  split_ifs
  · exact exteriorResidual_odd hodd y
  · simp

/-- The zero-extended actual residual is nonnegative on the whole
positive half-line and strictly positive on the right exterior. -/
theorem MemRestrictedFormDomain.exteriorResidualZero_nonneg {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f)
    (hne : ¬ f =ᵐ[volume] 0) (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    {y : ℝ} (hy : 0 < y) : 0 ≤ exteriorResidualZero f y := by
  unfold exteriorResidualZero
  split_ifs with hext
  · exact (hf.exteriorResidual_pos hodd hne hnonneg (by simpa only [abs_of_pos hy] using hext)).le
  · exact le_rfl

/-- Integrating the actual exterior residual against the interior kernel
is strictly positive whenever that actual quotient is integrable. -/
theorem MemRestrictedFormDomain.integral_exteriorResidualZero_div_sq_pos {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f)
    (hne : ¬ f =ᵐ[volume] 0) (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    {x : ℝ} (hx : 0 < x)
    (hi : Integrable (fun y : ℝ => exteriorResidualZero f y / (x - y) ^ 2)) :
    0 < ∫ y : ℝ, exteriorResidualZero f y / (x - y) ^ 2 := by
  have hsign : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] exteriorResidualZero f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hf.exteriorResidualZero_nonneg hodd hne hnonneg hy
  have hpos : volume {y : ℝ | 0 < y ∧ 0 < exteriorResidualZero f y} ≠ 0 := by
    intro hz
    have hsub : Ioo (1 : ℝ) 2 ⊆ {y : ℝ | 0 < y ∧ 0 < exteriorResidualZero f y} := by
      intro y hy
      refine ⟨by linarith [hy.1], ?_⟩
      have hya : 1 < |y| := hy.1.trans_le (le_abs_self y)
      rw [exteriorResidualZero, if_pos hya]
      exact hf.exteriorResidual_pos hodd hne hnonneg hy.1
    have hnull := measure_mono_null hsub hz
    exact ((Measure.measure_Ioo_pos volume).2 (by norm_num : (1 : ℝ) < 2)).ne' hnull
  exact integral_odd_quotient_sq_pos hx (exteriorResidualZero_odd hodd) hsign hpos hi

end Torsion.Spectral

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Exact exterior integral of the one-dimensional Cauchy derivative kernel. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Torsion.Spectral

private theorem right_kernel_data {s : ℝ} (hs : s < 1) :
    IntegrableOn (fun y : ℝ => 1 / (y - s) ^ 2) (Ioi (1 : ℝ)) ∧
    (∫ y in Ioi (1 : ℝ), 1 / (y - s) ^ 2) = 1 / (1 - s) := by
  have hd : ∀ y ∈ Ici (1 : ℝ), HasDerivAt (fun t : ℝ => -(t - s)⁻¹)
      (1 / (y - s) ^ 2) y := by
    intro y hy
    have hne : y - s ≠ 0 := by linarith [hy.out]
    simpa only [id_eq, neg_div, neg_neg] using! (((hasDerivAt_id y).sub_const s).inv hne).neg
  have hshift : Tendsto (fun y : ℝ => y - s) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-s) tendsto_id
  have ht : Tendsto (fun y : ℝ => -(y - s)⁻¹) atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_inv_atTop_zero.comp hshift).neg
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd (fun y _ => by positivity) ht
  refine ⟨hi, ?_⟩
  simpa only [zero_sub, neg_neg, one_div] using integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht

private theorem left_kernel_data {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun y : ℝ => 1 / (y - s) ^ 2) (Iio (-1 : ℝ)) ∧
    (∫ y in Iio (-1 : ℝ), 1 / (y - s) ^ 2) = 1 / (1 + s) := by
  obtain ⟨hi, hv⟩ := right_kernel_data (s := -s) (by linarith)
  have heq : (fun y : ℝ => 1 / (-y - s) ^ 2) = fun y => 1 / (y - -s) ^ 2 := by
    funext y
    congr 1
    ring
  have hleft : IntegrableOn (fun y : ℝ => 1 / (y - s) ^ 2) (Iic (-1 : ℝ)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, neg_preimage, neg_Iic, neg_neg]
    rw [heq]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hi
  refine ⟨(integrableOn_Iic_iff_integrableOn_Iio (by finiteness)).mp hleft, ?_⟩
  rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi (1 : ℝ)]
  rw [heq, hv]
  congr 1
  ring

private theorem exterior_eq_union : {y : ℝ | 1 < |y|} = Iio (-1 : ℝ) ∪ Ioi 1 := by
  ext y
  simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi]
  constructor
  · intro h
    rcases le_total 0 y with hy | hy
    · exact Or.inr (by simpa only [abs_of_nonneg hy] using h)
    · exact Or.inl (by rw [abs_of_nonpos hy] at h; linarith)
  · rintro (h | h)
    · rw [abs_of_neg (by linarith : y < 0)]
      linarith
    · rw [abs_of_pos (by linarith : 0 < y)]
      exact h

/-- The exterior squared reciprocal kernel is genuinely integrable for
an interior pole. -/
theorem integrableOn_exterior_inv_sub_sq {s : ℝ} (hs : |s| < 1) :
    IntegrableOn (fun y : ℝ => 1 / (y - s) ^ 2) {y : ℝ | 1 < |y|} := by
  rw [exterior_eq_union]
  exact (left_kernel_data (abs_lt.mp hs).1).1.union (right_kernel_data (abs_lt.mp hs).2).1

/-- Exact integral of the derivative kernel outside the restricted interval. -/
theorem integral_exterior_inv_sub_sq {s : ℝ} (hs : |s| < 1) :
    (∫ y in {y : ℝ | 1 < |y|}, 1 / (y - s) ^ 2) = 1 / (1 - s) + 1 / (1 + s) := by
  rw [exterior_eq_union, setIntegral_union (by
    apply disjoint_left.mpr
    intro y hy hy'
    linarith [hy.out, hy'.out]) measurableSet_Ioi
    (left_kernel_data (abs_lt.mp hs).1).1 (right_kernel_data (abs_lt.mp hs).2).1,
    (left_kernel_data (abs_lt.mp hs).1).2, (right_kernel_data (abs_lt.mp hs).2).2]
  ring

/-- A boundary-distance majorant suitable for the actual Tonelli argument. -/
theorem integral_exterior_inv_sub_sq_le {s : ℝ} (hs : |s| < 1) :
    (∫ y in {y : ℝ | 1 < |y|}, 1 / (y - s) ^ 2) ≤ 2 / (1 - |s|) := by
  rw [integral_exterior_inv_sub_sq hs]
  have hd : 0 < 1 - |s| := by linarith
  have h1 : 1 / (1 - s) ≤ 1 / (1 - |s|) :=
    one_div_le_one_div_of_le hd (by linarith [le_abs_self s])
  have h2 : 1 / (1 + s) ≤ 1 / (1 - |s|) :=
    one_div_le_one_div_of_le hd (by linarith [neg_le_abs s])
  calc
    _ ≤ 1 / (1 - |s|) + 1 / (1 - |s|) := add_le_add h1 h2
    _ = _ := by ring

end Torsion.Spectral

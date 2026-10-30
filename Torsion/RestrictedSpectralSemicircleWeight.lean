module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! An actual integrable majorant for the semicircle's Gagliardo kernel. -/
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace Torsion.Spectral

/-- The inverse square root of distance to a point is locally integrable,
including intervals containing the singular point. -/
theorem intervalIntegrable_inv_sqrt_abs (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => (Real.sqrt |x|)⁻¹) volume a b := by
  have hpos (c : ℝ) (hc : 0 ≤ c) :
      IntervalIntegrable (fun x : ℝ => (Real.sqrt |x|)⁻¹) volume 0 c := by
    have hpow := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := c)
      (by norm_num : (-1 : ℝ) < -1 / 2)
    rw [intervalIntegrable_iff] at hpow ⊢
    apply hpow.congr_fun _ measurableSet_uIoc
    intro x hx
    rw [uIoc_of_le hc] at hx
    dsimp only
    rw [abs_of_nonneg hx.1.le, Real.sqrt_eq_rpow,
      show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx.1.le]
  have hzero (c : ℝ) : IntervalIntegrable (fun x : ℝ => (Real.sqrt |x|)⁻¹) volume 0 c := by
    rcases le_total 0 c with hc | hc
    · exact hpos c hc
    · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
      simpa only [abs_neg] using hpos (-c) (neg_nonneg.mpr hc)
  exact (hzero a).symm.trans (hzero b)

/-- A positive integrable majorant, with the exact square-root endpoint
singularities and an integrable rational tail. -/
def semicircleKernelWeight (x : ℝ) : ℝ :=
  if |x| < 2 then (Real.sqrt |1 - x ^ 2|)⁻¹ else (1 + x ^ 2)⁻¹

theorem semicircleKernelWeight_nonneg (x : ℝ) : 0 ≤ semicircleKernelWeight x := by
  unfold semicircleKernelWeight
  split_ifs <;> positivity

private theorem semicircle_inv_sqrt_le_right {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt |1 - x ^ 2|)⁻¹ ≤ (Real.sqrt |x - 1|)⁻¹ := by
  by_cases hx1 : x = 1
  · simp [hx1]
  have hd : 0 < |x - 1| := abs_pos.mpr (sub_ne_zero.mpr hx1)
  have hsq : |x - 1| ≤ |1 - x ^ 2| := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ 1 + x), abs_sub_comm 1 x]
    nlinarith [abs_nonneg (x - 1)]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.sqrt_pos.mpr hd) (Real.sqrt_le_sqrt hsq)

/-- The concrete majorant is integrable on the entire real line. -/
theorem integrable_semicircleKernelWeight : Integrable semicircleKernelWeight := by
  let g : ℝ → ℝ := fun x => (Real.sqrt |1 - x ^ 2|)⁻¹
  have hgm : Measurable g := by unfold g; fun_prop
  have hright : IntegrableOn g (Icc (0 : ℝ) 2) := by
    have hshift : IntervalIntegrable (fun x : ℝ => (Real.sqrt |x - 1|)⁻¹) volume 0 2 := by
      convert (intervalIntegrable_inv_sqrt_abs (-1) 1).comp_sub_right 1 using 1 <;> norm_num
    have hi : IntegrableOn (fun x : ℝ => (Real.sqrt |x - 1|)⁻¹) (Icc (0 : ℝ) 2) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 2)).mp hshift
    apply hi.mono' hgm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_of_nonneg (by dsimp only [g]; positivity)]
    exact semicircle_inv_sqrt_le_right hx.1
  have hleft : IntegrableOn g (Icc (-2 : ℝ) 0) := by
    have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 2)).mpr hright
    have hn := ((IntervalIntegrable.iff_comp_neg (f := g)).mp hi).symm
    have heq : (fun x => g (-x)) = g := by funext x; simp [g]
    rw [heq, neg_zero] at hn
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-2 : ℝ) ≤ 0)).mp hn
  have hlocal : IntegrableOn g {x : ℝ | |x| < 2} := by
    apply (hleft.union hright).mono_set
    intro x hx
    change |x| < 2 at hx
    have hx' := abs_lt.mp hx
    rcases le_total x 0 with hx0 | hx0
    · exact Or.inl ⟨hx'.1.le, hx0⟩
    · exact Or.inr ⟨hx0, hx'.2.le⟩
  have hA : MeasurableSet {x : ℝ | |x| < 2} := isOpen_lt continuous_abs continuous_const |>.measurableSet
  have hi : Integrable ({x : ℝ | |x| < 2}.indicator g) := (integrable_indicator_iff hA).mpr hlocal
  have ht : Integrable ({x : ℝ | |x| < 2}ᶜ.indicator (fun x : ℝ => (1 + x ^ 2)⁻¹)) :=
    integrable_inv_one_add_sq.indicator hA.compl
  apply (hi.add ht).congr
  filter_upwards [] with x
  by_cases hx : |x| < 2 <;> simp [semicircleKernelWeight, hx, g]

theorem semicircleKernelWeight_integrable : Integrable semicircleKernelWeight :=
  integrable_semicircleKernelWeight

end Torsion.Spectral

module

public import Torsion.Curvature
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Strict curvature from actual eigenfunction concavity

The interval-integral estimates and strict tangent-line bounds used in
Lemma 6.1 are derived here from concavity, differentiability, and positivity
of the eigenfunction. They are not additional scalar assumptions. The final
form applies to any velocity with derivative `a * φ` and an interior zero.
-/

noncomputable section
open Set MeasureTheory

namespace Torsion.Curvature

/-- A differentiable concave function lies below its tangent at every other
point of its convexity set. -/
theorem concave_le_tangent {S : Set ℝ} {φ : ℝ → ℝ} (hc : ConcaveOn ℝ S φ)
    {x y p : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hp : HasDerivAt φ p x) :
    φ y ≤ φ x + (y - x) * p := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have hh := hc.slope_le_of_hasDerivAt hx hy hxy hp
    rw [slope_def_field] at hh
    have hm := (div_le_iff₀ (sub_pos.2 hxy)).mp hh
    nlinarith
  · subst y
    simp
  · have hh := hc.le_slope_of_hasDerivAt hy hx hyx hp
    rw [slope_def_field] at hh
    have hm := (le_div_iff₀ (sub_pos.2 hyx)).mp hh
    nlinarith

/-- The strict curvature numerator for the actual primitive velocity.
All tangent and integral estimates are derived from the hypotheses on `φ`. -/
theorem positive_of_concave_primitive {a x₀ x : ℝ} {φ : ℝ → ℝ}
    (ha : 0 < a) (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ y ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ y)
    (hp : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < φ y)
    (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < a * (φ x) ^ 2 - (a * ∫ s in x₀..x, φ s) * deriv φ x := by
  let v : ℝ := a * ∫ s in x₀..x, φ s
  change 0 < a * (φ x) ^ 2 - v * deriv φ x
  have hcont : ContinuousOn φ (Ioo (0 : ℝ) 1) :=
    fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hdx := (hd x hx).hasDerivAt
  have ht₀ := concave_le_tangent hc hx hx₀ hdx
  by_cases hprod : v * deriv φ x ≤ 0
  · exact positive_of_nonpos_product ha (hp x hx) hprod
  have hprodpos : 0 < v * deriv φ x := lt_of_not_ge hprod
  apply positive_of_tangent_bound ha (hp x hx) (d := |x - x₀|)
  · rcases lt_trichotomy x₀ x with horder | horder | horder
    · have hsub : Icc x₀ x ⊆ Ioo (0 : ℝ) 1 := fun y hy =>
        ⟨hx₀.1.trans_le hy.1, hy.2.trans_lt hx.2⟩
      have hint : IntervalIntegrable φ volume x₀ x :=
        (hcont.mono hsub).intervalIntegrable_of_Icc horder.le
      have hipos : 0 < ∫ s in x₀..x, φ s :=
        intervalIntegral.intervalIntegral_pos_of_pos_on hint
          (fun y hy => hp y (hsub (Ioo_subset_Icc_self hy))) horder
      have hvpos : 0 < v := mul_pos ha hipos
      have hdpos : 0 < deriv φ x := by
        by_contra hh
        exact (not_le_of_gt hprodpos)
          (mul_nonpos_of_nonneg_of_nonpos hvpos.le (le_of_not_gt hh))
      have hbound : (∫ s in x₀..x, φ s) ≤ (x - x₀) * φ x := by
        calc
          _ ≤ ∫ _s in x₀..x, φ x :=
            intervalIntegral.integral_mono_on horder.le hint intervalIntegrable_const (by
              intro y hy
              have ht := concave_le_tangent hc hx (hsub hy) hdx
              have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hy.2) hdpos.le
              linarith)
          _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]
      rw [abs_of_pos hvpos, abs_of_pos (sub_pos.2 horder)]
      exact (mul_le_mul_of_nonneg_left hbound ha.le).trans_eq (by ring)
    · subst x
      simp [v] at hprodpos
    · have hsub : Icc x x₀ ⊆ Ioo (0 : ℝ) 1 := fun y hy =>
        ⟨hx.1.trans_le hy.1, hy.2.trans_lt hx₀.2⟩
      have hint : IntervalIntegrable φ volume x x₀ :=
        (hcont.mono hsub).intervalIntegrable_of_Icc horder.le
      have hipos : 0 < ∫ s in x..x₀, φ s :=
        intervalIntegral.intervalIntegral_pos_of_pos_on hint
          (fun y hy => hp y (hsub (Ioo_subset_Icc_self hy))) horder
      have hv_eq : v = -(a * ∫ s in x..x₀, φ s) := by
        dsimp [v]
        rw [intervalIntegral.integral_symm]
        ring
      have hvneg : v < 0 := by rw [hv_eq]; exact neg_neg_of_pos (mul_pos ha hipos)
      have hdneg : deriv φ x < 0 := by
        by_contra hh
        exact (not_le_of_gt hprodpos)
          (mul_nonpos_of_nonpos_of_nonneg hvneg.le (le_of_not_gt hh))
      have hbound : (∫ s in x..x₀, φ s) ≤ (x₀ - x) * φ x := by
        calc
          _ ≤ ∫ _s in x..x₀, φ x :=
            intervalIntegral.integral_mono_on horder.le hint intervalIntegrable_const (by
              intro y hy
              have ht := concave_le_tangent hc hx (hsub hy) hdx
              have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hy.1) hdneg.le
              linarith)
          _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]
      calc
        |v| = a * ∫ s in x..x₀, φ s := by rw [abs_of_neg hvneg, hv_eq]; ring
        _ ≤ a * ((x₀ - x) * φ x) := mul_le_mul_of_nonneg_left hbound ha.le
        _ = a * |x - x₀| * φ x := by rw [abs_of_neg (sub_neg.2 horder)]; ring
  · rcases lt_trichotomy x₀ x with horder | horder | horder
    · have hsub : Icc x₀ x ⊆ Ioo (0 : ℝ) 1 := fun y hy =>
        ⟨hx₀.1.trans_le hy.1, hy.2.trans_lt hx.2⟩
      have hint : IntervalIntegrable φ volume x₀ x :=
        (hcont.mono hsub).intervalIntegrable_of_Icc horder.le
      have hvpos : 0 < v := mul_pos ha
        (intervalIntegral.intervalIntegral_pos_of_pos_on hint
          (fun y hy => hp y (hsub (Ioo_subset_Icc_self hy))) horder)
      have hdpos : 0 < deriv φ x := by
        by_contra hh
        exact (not_le_of_gt hprodpos)
          (mul_nonpos_of_nonneg_of_nonpos hvpos.le (le_of_not_gt hh))
      rw [abs_of_pos (sub_pos.2 horder), abs_of_pos hdpos]
      nlinarith [hp x₀ hx₀]
    · subst x
      simp [v] at hprodpos
    · have hsub : Icc x x₀ ⊆ Ioo (0 : ℝ) 1 := fun y hy =>
        ⟨hx.1.trans_le hy.1, hy.2.trans_lt hx₀.2⟩
      have hint : IntervalIntegrable φ volume x x₀ :=
        (hcont.mono hsub).intervalIntegrable_of_Icc horder.le
      have hipos : 0 < ∫ s in x..x₀, φ s :=
        intervalIntegral.intervalIntegral_pos_of_pos_on hint
          (fun y hy => hp y (hsub (Ioo_subset_Icc_self hy))) horder
      have hvneg : v < 0 := by
        dsimp [v]
        rw [intervalIntegral.integral_symm]
        nlinarith [mul_pos ha hipos]
      have hdneg : deriv φ x < 0 := by
        by_contra hh
        exact (not_le_of_gt hprodpos)
          (mul_nonpos_of_nonpos_of_nonneg hvneg.le (le_of_not_gt hh))
      rw [abs_of_neg (sub_neg.2 horder), abs_of_neg hdneg]
      nlinarith [hp x₀ hx₀]

/-- The primitive representation follows from the actual velocity ODE and
its value at the interior zero, by the fundamental theorem of calculus. -/
theorem velocity_eq_primitive {a x₀ x : ℝ} {φ v : ℝ → ℝ}
    (hφ : ContinuousOn φ (Ioo (0 : ℝ) 1))
    (hv : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt v (a * φ y) y)
    (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hv₀ : v x₀ = 0) : v x = a * ∫ s in x₀..x, φ s := by
  have hsub : uIcc x₀ x ⊆ Ioo (0 : ℝ) 1 := ordConnected_Ioo.uIcc_subset hx₀ hx
  have hint : IntervalIntegrable (fun y => a * φ y) volume x₀ x :=
    ((hφ.mono hsub).const_smul a).intervalIntegrable
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hv y (hsub hy)) hint
  rw [intervalIntegral.integral_const_mul, hv₀, sub_zero] at heq
  exact heq.symm

/-- Lemma 6.1's strict-curvature estimate from genuine concavity and the
velocity differential equation; no separate tangent or velocity bound. -/
theorem positive_of_concavity_and_velocity {a x₀ x : ℝ} {φ v : ℝ → ℝ}
    (ha : 0 < a) (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ y ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ y)
    (hp : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < φ y)
    (hv : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt v (a * φ y) y)
    (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hv₀ : v x₀ = 0) : 0 < a * (φ x) ^ 2 - v x * deriv φ x := by
  rw [velocity_eq_primitive
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt) hv hx₀ hx hv₀]
  exact positive_of_concave_primitive ha hc hd hp hx₀ hx

end Torsion.Curvature

end

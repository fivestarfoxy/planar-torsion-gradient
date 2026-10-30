module

public import Torsion.SobolevComposition
public import Torsion.SmoothPositivePart
public import Torsion.L2Dominated

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The positive-part chain rule in the concrete Sobolev graph

Flat smooth primitives fixing zero preserve the compact core. Their values
converge in L² by domination by the original value, and their bounded slopes
converge pointwise including at zero. Closedness of the actual graph supplies
the positive part and its genuine weak gradient without an additional
level-set-gradient assumption.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

private theorem norm_positive_part_le (t : ℝ) : ‖max t 0‖ ≤ ‖t‖ := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht]
  · rw [max_eq_right (le_of_not_ge ht), norm_zero]
    exact norm_nonneg _

/-- The concrete positive-part chain rule, first in bounded-coefficient form. -/
theorem MemH10.pos_part_smul {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) :
    MemH10 D (fun x => max (u x) 0)
      (fun x => (if 0 < u x then (1 : ℝ) else 0) • g x) := by
  have han (n : ℕ) :
      AEStronglyMeasurable (fun x => SmoothPositivePart.slope n (u x)) volume :=
    (SmoothPositivePart.slope_contDiff n).continuous.comp_aestronglyMeasurable hu.1.aestronglyMeasurable
  have halim : ∀ᵐ x ∂volume,
      Tendsto (fun n => SmoothPositivePart.slope n (u x)) atTop
        (𝓝 (if 0 < u x then (1 : ℝ) else 0)) :=
    Eventually.of_forall (fun x => SmoothPositivePart.tendsto_slope (u x))
  have ha : AEStronglyMeasurable (fun x => if 0 < u x then (1 : ℝ) else 0) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop han halim
  have hbn (n : ℕ) : ∀ᵐ x ∂volume, ‖SmoothPositivePart.slope n (u x)‖ ≤ (1 : ℝ) :=
    Eventually.of_forall (fun x => SmoothPositivePart.slope_norm_le_one n (u x))
  have hba : ∀ᵐ x ∂volume, ‖if 0 < u x then (1 : ℝ) else 0‖ ≤ (1 : ℝ) := by
    apply Eventually.of_forall
    intro x
    split_ifs <;> norm_num
  have hg : MemLp (fun x => (if 0 < u x then (1 : ℝ) else 0) • g x) 2 volume :=
    memLp_bounded_coeff_smul ha hu.2.1 hba
  have hseq (n : ℕ) := hu.comp_smooth_lipschitz
    (SmoothPositivePart.approx_contDiff n) (SmoothPositivePart.approx_lipschitz n)
    (SmoothPositivePart.approx_zero n)
  have hval : Tendsto (fun n => eLpNorm
      (fun x => SmoothPositivePart.approx n (u x) - max (u x) 0) 2 volume) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_dominated (B := fun x => 2 * ‖u x‖)
    · intro n
      exact ((SmoothPositivePart.approx_contDiff n).continuous.comp_aestronglyMeasurable
        hu.1.aestronglyMeasurable).sub hu.1.pos_part.aestronglyMeasurable
    · have hsq : Integrable (fun x => ‖u x‖ ^ 2) volume :=
        (memLp_two_iff_integrable_sq_norm hu.1.aestronglyMeasurable).mp hu.1
      simpa only [mul_pow] using hsq.const_mul ((2 : ℝ) ^ 2)
    · intro n
      apply Eventually.of_forall
      intro x
      calc
        ‖SmoothPositivePart.approx n (u x) - max (u x) 0‖ ≤
            ‖SmoothPositivePart.approx n (u x)‖ + ‖max (u x) 0‖ := norm_sub_le _ _
        _ ≤ 2 * ‖u x‖ := by
          linarith [SmoothPositivePart.approx_norm_le n (u x), norm_positive_part_le (u x)]
    · apply Eventually.of_forall
      intro x
      simpa only [sub_self] using (SmoothPositivePart.tendsto_approx (u x)).sub_const (max (u x) 0)
  have hprod := tendsto_eLpNorm_bounded_coeff_smul han ha hu.2.1 hbn hba halim
  have hgrad : Tendsto (fun n => eLpNorm
      (fun x => deriv (SmoothPositivePart.approx n) (u x) • g x -
        (if 0 < u x then (1 : ℝ) else 0) • g x) 2 volume) atTop (𝓝 0) := by
    simpa only [SmoothPositivePart.approx_deriv, sub_smul] using hprod
  exact MemH10.of_tendsto hu.1.pos_part hg hseq hval hgrad

/-- The positive part belongs to the actual zero-boundary Sobolev graph; its
weak gradient is the original gradient on `{u > 0}` and zero elsewhere. -/
theorem MemH10.pos_part {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) :
    MemH10 D (fun x => max (u x) 0) (fun x => if 0 < u x then g x else 0) := by
  have heq : (fun x => (if 0 < u x then (1 : ℝ) else 0) • g x) =
      (fun x => if 0 < u x then g x else 0) := by
    funext x
    split_ifs <;> simp
  rw [← heq]
  exact hu.pos_part_smul

end Torsion

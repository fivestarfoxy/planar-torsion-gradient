import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-!
# Pointwise signs of continuous interior representatives

Continuity on an open set promotes an almost-everywhere nonnegative sign
to a pointwise nonnegative sign. Strict positivity almost everywhere only
gives existence of positive points in each non-null interval here; the
separate strict positivity problem is not replaced by a continuity claim.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Torsion.Spectral

/-- A continuous function on an open set inherits an almost-everywhere
nonnegative sign at every point of that set. -/
theorem nonneg_on_open_of_continuousOn_ae_nonneg {g : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hg : ContinuousOn g U)
    (hpos : ∀ᵐ x : ℝ ∂volume.restrict U, 0 ≤ g x) :
    ∀ x ∈ U, 0 ≤ g x := by
  have hmin : (fun x => min (g x) 0) =ᵐ[volume.restrict U] (fun _ => 0) := by
    filter_upwards [hpos] with x hx
    exact min_eq_right hx
  have heq := Measure.eqOn_open_of_ae_eq hmin hU
    (fun x hx => (hg x hx).min continuousWithinAt_const) continuousOn_const
  intro x hx
  exact (min_eq_right_iff).1 (heq hx)

/-- The interval version used for the actual positive-half spectral
representative; continuity is needed only in the open interval. -/
theorem nonneg_on_Ioo_of_continuousOn_ae_nonneg {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Ioo a b))
    (hpos : ∀ᵐ x : ℝ ∂volume.restrict (Ioo a b), 0 ≤ g x) :
    ∀ x ∈ Ioo a b, 0 ≤ g x :=
  nonneg_on_open_of_continuousOn_ae_nonneg isOpen_Ioo hg hpos

/-- An almost-everywhere strictly positive function has a positive point
on each non-null set. Measurability and continuity are unnecessary. -/
theorem exists_mem_pos_of_ae_pos {g : ℝ → ℝ} {S : Set ℝ}
    (hS : volume S ≠ 0) (hpos : ∀ᵐ x : ℝ ∂volume.restrict S, 0 < g x) :
    ∃ x ∈ S, 0 < g x := by
  by_contra h
  push_neg at h
  have hnull : ∀ᵐ x : ℝ ∂volume, x ∉ S := by
    filter_upwards [ae_imp_of_ae_restrict hpos] with x hx
    exact fun hxS => not_lt_of_ge (h x hxS) (hx hxS)
  apply hS
  simpa only [ae_iff, not_not] using hnull

/-- In particular every nonempty open interval contains a positive point
if the function is strictly positive almost everywhere on it. -/
theorem exists_pos_on_Ioo_of_ae_pos {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hpos : ∀ᵐ x : ℝ ∂volume.restrict (Ioo a b), 0 < g x) :
    ∃ x ∈ Ioo a b, 0 < g x :=
  exists_mem_pos_of_ae_pos ((Measure.measure_Ioo_pos volume).2 hab).ne' hpos

/-- Strict positivity almost everywhere on the positive half-interval
therefore supplies a positive point in every contained nonempty interval. -/
theorem exists_pos_on_subinterval_of_ae_pos {g : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b)
    (hpos : ∀ᵐ x : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < g x) :
    ∃ x ∈ Ioo a b, 0 < g x := by
  apply exists_pos_on_Ioo_of_ae_pos hab
  have hsub : Ioo a b ⊆ Ioo (0 : ℝ) 1 :=
    fun x hx => ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩
  exact ae_restrict_of_ae_restrict_of_subset hsub hpos

end Torsion.Spectral

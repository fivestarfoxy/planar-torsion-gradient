module

public import Torsion.SobolevPositivePart
public import Torsion.SobolevSupport
public import Torsion.Sobolev
public import Torsion.BoundedDomains

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Nonnegativity of actual weak torsion solutions

The negative part is an actual admissible Sobolev test by the proved lattice
chain rule. Its energy pairing is nonpositive and its load is nonnegative,
forcing the integral of its value to vanish. On a bounded domain this value is
integrable, so the torsion value is nonnegative almost everywhere. No maximum
principle or abstract positivity assumption is used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- The weak torsion value is nonnegative a.e. on every bounded domain. No
boundary regularity or even domain measurability is required. -/
theorem IsWeakTorsion.nonneg_ae_restrict {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hbounded : Bornology.IsBounded D) :
    ∀ᵐ x ∂volume.restrict D, 0 ≤ u x := by
  letI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr hbounded.measure_lt_top.ne
  have hneg := hu.1.neg.pos_part
  have heq := hu.2 (fun x => max (-u x) 0)
    (fun x => if 0 < -u x then -g x else 0) hneg
  have henergy : (∫ x in D,
      inner (𝕜 := ℝ) (g x) (if 0 < -u x then -g x else 0)) ≤ 0 := by
    apply integral_nonpos
    intro x
    change inner (𝕜 := ℝ) (g x) (if 0 < -u x then -g x else 0) ≤ (0 : ℝ)
    by_cases hx : 0 < -u x
    · simp only [if_pos hx, inner_neg_right, real_inner_self_eq_norm_sq]
      exact neg_nonpos.mpr (sq_nonneg _)
    · simp only [if_neg hx, inner_zero_right, le_refl]
  have hload : (∫ x in D, max (-u x) 0) = 0 := by
    apply le_antisymm
    · rw [← heq]
      exact henergy
    · exact integral_nonneg (fun x => le_max_right _ _)
  have hint : Integrable (fun x => max (-u x) 0) (volume.restrict D) :=
    MemLp.integrable (by norm_num) (hu.1.1.neg_part.restrict D)
  have hzero := (integral_eq_zero_iff_of_nonneg (fun x => le_max_right (-u x) 0) hint).mp hload
  filter_upwards [hzero] with x hx
  have hle : -u x ≤ 0 := (le_max_left (-u x) 0).trans (le_of_eq hx)
  linarith

/-- Zero extension gives global nonnegativity of the actual torsion value. -/
theorem IsWeakTorsion.nonneg_ae {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hbounded : Bornology.IsBounded D) :
    ∀ᵐ x ∂volume, 0 ≤ u x := by
  apply ae_of_ae_restrict_of_ae_restrict_compl D (hu.nonneg_ae_restrict hbounded)
  filter_upwards [hu.1.value_ae_zero_off] with x hx
  simp only [Pi.zero_apply] at hx
  simp only [hx, le_refl]

/-- The constructed weak solution records inherit nonnegativity from their
actual equation on every bounded domain. -/
theorem DirichletSolution.nonneg_ae {D : Set Plane}
    (s : DirichletSolution D) (hbounded : Bornology.IsBounded D) :
    ∀ᵐ x ∂volume, 0 ≤ s.value x :=
  s.weakEquation.nonneg_ae hbounded

end Torsion

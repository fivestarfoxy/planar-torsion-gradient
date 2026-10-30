import Torsion.SobolevPositivePart
import Torsion.WeakGradient

/-!
# Lattice calculus for the actual zero-boundary Sobolev graph

Positive-part closure is proved in `SobolevPositivePart` by flat smooth
approximation. Uniqueness of distributional gradients then forces the weak
gradient to vanish on the zero level, and yields the usual min/max formulas.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- A genuine weak gradient vanishes almost everywhere on the zero level of
its Sobolev value. This follows from positive/negative part decomposition and
the proved uniqueness of distributional gradients. -/
theorem MemH10.gradient_ae_zero_on_zero {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : MemH10 D u g) :
    ∀ᵐ x ∂volume, u x = 0 → g x = 0 := by
  have hparts := hu.pos_part.sub hu.neg.pos_part
  have hvalues : (fun x => Max.max (u x) 0 - Max.max (-u x) 0) =ᵐ[volume] u :=
    Eventually.of_forall (fun x => max_zero_sub_max_neg_zero_eq_self (u x))
  have hgrad := hparts.gradient_ae_eq_of_value_ae_eq hu hvalues
  filter_upwards [hgrad] with x hx
  intro hzero
  simpa only [hzero, neg_zero, lt_self_iff_false, if_false, sub_self] using hx.symm

/-- Gradients of two Sobolev functions agree almost everywhere on their equal
level, including when their original zero-trace domains differ. -/
theorem MemH10.gradient_ae_eq_on_equal {D : Set Plane} {u v : Plane → ℝ}
    {g h : Plane → Plane} (hu : MemH10 D u g) (hv : MemH10 D v h) :
    ∀ᵐ x ∂volume, u x = v x → g x = h x := by
  have hzero := (hu.sub hv).gradient_ae_zero_on_zero
  filter_upwards [hzero] with x hx
  intro huv
  exact sub_eq_zero.mp (hx (sub_eq_zero.mpr huv))

/-- Pointwise minimum is in the actual Sobolev graph, with the expected
piecewise weak gradient. -/
theorem MemH10.min {D : Set Plane} {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : MemH10 D u g) (hv : MemH10 D v h) :
    MemH10 D (fun x => Min.min (u x) (v x))
      (fun x => if u x ≤ v x then g x else h x) := by
  have hmin := hu.sub (hu.sub hv).pos_part
  have hvalue : (fun x => u x - Max.max (u x - v x) 0) = (fun x => Min.min (u x) (v x)) := by
    funext x
    by_cases huv : u x ≤ v x
    · rw [max_eq_right (sub_nonpos.mpr huv), sub_zero, min_eq_left huv]
    · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge huv)), min_eq_right (le_of_not_ge huv)]
      ring
  have hgradient : (fun x => g x - (if 0 < u x - v x then g x - h x else 0)) =
      (fun x => if u x ≤ v x then g x else h x) := by
    funext x
    by_cases huv : u x ≤ v x
    · simp [huv, not_lt.mpr huv, sub_pos]
    · simp [huv, sub_pos.mpr (lt_of_not_ge huv)]
  simpa only [hvalue, hgradient] using hmin

/-- Pointwise maximum is in the actual Sobolev graph. -/
theorem MemH10.max {D : Set Plane} {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : MemH10 D u g) (hv : MemH10 D v h) :
    MemH10 D (fun x => Max.max (u x) (v x))
      (fun x => if u x < v x then h x else g x) := by
  have hmax := hu.add (hv.sub hu).pos_part
  have hvalue : (fun x => u x + Max.max (v x - u x) 0) = (fun x => Max.max (u x) (v x)) := by
    funext x
    by_cases huv : u x < v x
    · rw [max_eq_left (sub_nonneg.mpr huv.le), max_eq_right huv.le]
      ring
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt huv)), add_zero,
        max_eq_left (le_of_not_gt huv)]
  have hgradient : (fun x => g x + (if 0 < v x - u x then h x - g x else 0)) =
      (fun x => if u x < v x then h x else g x) := by
    funext x
    by_cases huv : u x < v x
    · simp [huv, sub_pos.mpr huv]
    · simp [huv, sub_pos]
  simpa only [hvalue, hgradient] using hmax

end Torsion

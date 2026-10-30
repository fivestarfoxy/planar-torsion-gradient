import Torsion.Definitions
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Calculus.Deriv.AffineMap

/-!
# Regular convex levels and strict convexity of sublevel closures

These are geometric facts about actual differentiable functions and their
actual Euclidean level sets. In particular a level above some function value
cannot have zero derivative for a convex differentiable function.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Torsion

theorem fderiv_ne_zero_of_convex_level {F : Plane → ℝ}
    (hc : ConvexOn ℝ univ F) (hd : Differentiable ℝ F)
    {c : ℝ} (hbelow : ∃ y, F y < c) {x : Plane} (hx : F x = c) :
    fderiv ℝ F x ≠ 0 := by
  intro hz
  obtain ⟨y, hy⟩ := hbelow
  let l : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap x y
  have hconv : ConvexOn ℝ univ (F ∘ l) := by
    simpa using hc.comp_affineMap l
  have hfd : HasFDerivAt F (0 : Plane →L[ℝ] ℝ) x := by simpa only [hz] using (hd x).hasFDerivAt
  have hder : HasDerivAt (F ∘ l) 0 0 := by
    simpa using hfd.comp_hasDerivAt_of_eq 0
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := 0))
      (by simp [l])
  have h := hconv.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    zero_lt_one hder
  simp only [slope_def_field, sub_zero, div_one, Function.comp_apply,
    l, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, hx] at h
  linarith

theorem sublevel_le_of_mem_closure {F : Plane → ℝ} (hF : Continuous F)
    {c : ℝ} {x : Plane} (hx : x ∈ closure {z | F z < c}) : F x ≤ c := by
  exact closure_minimal (show {z | F z < c} ⊆ {z | F z ≤ c} from
    fun z hz => show F z ≤ c from le_of_lt hz) (isClosed_le hF continuous_const) hx

theorem sublevel_eq_of_mem_frontier {F : Plane → ℝ} (hF : Continuous F)
    {c : ℝ} {x : Plane} (hx : x ∈ frontier {z | F z < c}) : F x = c := by
  apply le_antisymm (sublevel_le_of_mem_closure hF hx.1)
  apply not_lt.mp
  intro hlt
  apply hx.2
  exact (isOpen_lt hF continuous_const).interior_eq.symm ▸ hlt

/-- A strictly convex continuous defining function makes the closure of its
strict sublevel strictly convex in the geometric sense, including boundary
points. -/
theorem strictConvex_closure_sublevel {F : Plane → ℝ}
    (hF : Continuous F) (hc : StrictConvexOn ℝ univ F) (c : ℝ) :
    StrictConvex ℝ (closure {x | F x < c}) := by
  intro x hx y hy hxy a b ha hb hab
  have hEin : {z | F z < c} ⊆ interior (closure {z | F z < c}) := by
    calc
      _ = interior {z | F z < c} := (isOpen_lt hF continuous_const).interior_eq.symm
      _ ⊆ _ := interior_mono subset_closure
  apply hEin
  have hstrict := hc.2 (mem_univ x) (mem_univ y) hxy ha hb hab
  have hxle := sublevel_le_of_mem_closure hF hx
  have hyle := sublevel_le_of_mem_closure hF hy
  change F (a • x + b • y) < c
  have hle : a * F x + b * F y ≤ c := by
    calc
      _ ≤ a * c + b * c := add_le_add (mul_le_mul_of_nonneg_left hxle ha.le)
        (mul_le_mul_of_nonneg_left hyle hb.le)
      _ = c := by rw [← add_mul, hab, one_mul]
  exact hstrict.trans_le hle

end Torsion

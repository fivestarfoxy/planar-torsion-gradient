module

public import Torsion.SobolevLatticeContinuity
public import Torsion.SobolevLattice

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Strong H¹ continuity of minimum and maximum

The actual positive-part continuity theorem is combined with linear L²
convergence, using `min u v = u - (u-v)⁺` and
`max u v = u + (v-u)⁺`. Both the value and the concrete weak-gradient
coordinates converge; no lattice-continuity premise is introduced.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Addition preserves simultaneous strong L² limits of two sequences. -/
theorem tendsto_eLpNorm_add_pair
    {X E : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E]
    {fₙ gₙ : ℕ → X → E} {f g : X → E}
    (hfn : ∀ n, MemLp (fₙ n) 2 μ) (hf : MemLp f 2 μ)
    (hgn : ∀ n, MemLp (gₙ n) 2 μ) (hg : MemLp g 2 μ)
    (hflim : Tendsto (fun n => eLpNorm (fun x => fₙ n x - f x) 2 μ) atTop (𝓝 0))
    (hglim : Tendsto (fun n => eLpNorm (fun x => gₙ n x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => (fₙ n x + gₙ n x) - (f x + g x)) 2 μ)
      atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => eLpNorm (fun x => fₙ n x - f x) 2 μ +
      eLpNorm (fun x => gₙ n x - g x) 2 μ) atTop (𝓝 0) := by
    simpa only [add_zero] using hflim.add hglim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro n
  dsimp only
  have heq : (fun x => (fₙ n x + gₙ n x) - (f x + g x)) =
      (fun x => fₙ n x - f x) + (fun x => gₙ n x - g x) := by
    funext x
    simp only [Pi.add_apply]
    abel
  rw [heq]
  exact eLpNorm_add_le (by norm_num)

/-- Subtraction preserves simultaneous strong L² limits of two sequences. -/
theorem tendsto_eLpNorm_sub_pair
    {X E : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E]
    {fₙ gₙ : ℕ → X → E} {f g : X → E}
    (hfn : ∀ n, MemLp (fₙ n) 2 μ) (hf : MemLp f 2 μ)
    (hgn : ∀ n, MemLp (gₙ n) 2 μ) (hg : MemLp g 2 μ)
    (hflim : Tendsto (fun n => eLpNorm (fun x => fₙ n x - f x) 2 μ) atTop (𝓝 0))
    (hglim : Tendsto (fun n => eLpNorm (fun x => gₙ n x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => (fₙ n x - gₙ n x) - (f x - g x)) 2 μ)
      atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => eLpNorm (fun x => fₙ n x - f x) 2 μ +
      eLpNorm (fun x => gₙ n x - g x) 2 μ) atTop (𝓝 0) := by
    simpa only [add_zero] using hflim.add hglim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro n
  dsimp only
  have heq : (fun x => (fₙ n x - gₙ n x) - (f x - g x)) =
      (fun x => fₙ n x - f x) - (fun x => gₙ n x - g x) := by
    funext x
    simp only [Pi.sub_apply]
    abel
  rw [heq]
  exact eLpNorm_sub_le (by norm_num)

private theorem min_value_repr (u v : ℝ) : u - max (u - v) 0 = min u v := by
  by_cases huv : u ≤ v
  · rw [max_eq_right (sub_nonpos.mpr huv), sub_zero, min_eq_left huv]
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge huv)), min_eq_right (le_of_not_ge huv)]
    ring

private theorem min_gradient_repr (u v : ℝ) (g h : Plane) :
    g - (if 0 < u - v then g - h else 0) = if u ≤ v then g else h := by
  by_cases huv : u ≤ v
  · simp [huv, not_lt.mpr huv, sub_pos]
  · simp [huv, sub_pos.mpr (lt_of_not_ge huv)]

private theorem max_value_repr (u v : ℝ) : u + max (v - u) 0 = max u v := by
  by_cases huv : u < v
  · rw [max_eq_left (sub_nonneg.mpr huv.le), max_eq_right huv.le]
    ring
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt huv)), add_zero,
      max_eq_left (le_of_not_gt huv)]

private theorem max_gradient_repr (u v : ℝ) (g h : Plane) :
    g + (if 0 < v - u then h - g else 0) = if u < v then h else g := by
  by_cases huv : u < v
  · simp [huv, sub_pos.mpr huv]
  · simp [huv, sub_pos]

/-- Strong convergence in the actual Sobolev graph is preserved by minimum,
including the piecewise weak-gradient formula. -/
theorem MemH10.tendsto_eLpNorm_min {D : Set Plane}
    {u v : Plane → ℝ} {g h : Plane → Plane}
    {uₙ vₙ : ℕ → Plane → ℝ} {gₙ hₙ : ℕ → Plane → Plane}
    (hu : MemH10 D u g) (hv : MemH10 D v h)
    (hun : ∀ n, MemH10 D (uₙ n) (gₙ n))
    (hvn : ∀ n, MemH10 D (vₙ n) (hₙ n))
    (huval : Tendsto (fun n => eLpNorm (fun x => uₙ n x - u x) 2 volume) atTop (𝓝 0))
    (hugrad : Tendsto (fun n => eLpNorm (fun x => gₙ n x - g x) 2 volume) atTop (𝓝 0))
    (hvval : Tendsto (fun n => eLpNorm (fun x => vₙ n x - v x) 2 volume) atTop (𝓝 0))
    (hvgrad : Tendsto (fun n => eLpNorm (fun x => hₙ n x - h x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Min.min (uₙ n x) (vₙ n x) - Min.min (u x) (v x))
      2 volume) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun x =>
      (if uₙ n x ≤ vₙ n x then gₙ n x else hₙ n x) -
      (if u x ≤ v x then g x else h x)) 2 volume) atTop (𝓝 0) := by
  have hdval := tendsto_eLpNorm_sub_pair (fun n => (hun n).1) hu.1
    (fun n => (hvn n).1) hv.1 huval hvval
  have hdgrad := tendsto_eLpNorm_sub_pair (fun n => (hun n).2.1) hu.2.1
    (fun n => (hvn n).2.1) hv.2.1 hugrad hvgrad
  have hp := (hu.sub hv).tendsto_eLpNorm_pos_part
    (fun n => (hun n).sub (hvn n)) hdval hdgrad
  constructor
  · have hl := tendsto_eLpNorm_sub_pair (fun n => (hun n).1) hu.1
      (fun n => ((hun n).sub (hvn n)).1.pos_part) (hu.sub hv).1.pos_part huval hp.1
    simpa only [min_value_repr] using hl
  · have hl := tendsto_eLpNorm_sub_pair (fun n => (hun n).2.1) hu.2.1
      (fun n => ((hun n).sub (hvn n)).pos_part.2.1) (hu.sub hv).pos_part.2.1 hugrad hp.2
    simpa only [min_gradient_repr] using hl

/-- Strong convergence in the actual Sobolev graph is preserved by maximum. -/
theorem MemH10.tendsto_eLpNorm_max {D : Set Plane}
    {u v : Plane → ℝ} {g h : Plane → Plane}
    {uₙ vₙ : ℕ → Plane → ℝ} {gₙ hₙ : ℕ → Plane → Plane}
    (hu : MemH10 D u g) (hv : MemH10 D v h)
    (hun : ∀ n, MemH10 D (uₙ n) (gₙ n))
    (hvn : ∀ n, MemH10 D (vₙ n) (hₙ n))
    (huval : Tendsto (fun n => eLpNorm (fun x => uₙ n x - u x) 2 volume) atTop (𝓝 0))
    (hugrad : Tendsto (fun n => eLpNorm (fun x => gₙ n x - g x) 2 volume) atTop (𝓝 0))
    (hvval : Tendsto (fun n => eLpNorm (fun x => vₙ n x - v x) 2 volume) atTop (𝓝 0))
    (hvgrad : Tendsto (fun n => eLpNorm (fun x => hₙ n x - h x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Max.max (uₙ n x) (vₙ n x) - Max.max (u x) (v x))
      2 volume) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun x =>
      (if uₙ n x < vₙ n x then hₙ n x else gₙ n x) -
      (if u x < v x then h x else g x)) 2 volume) atTop (𝓝 0) := by
  have hdval := tendsto_eLpNorm_sub_pair (fun n => (hvn n).1) hv.1
    (fun n => (hun n).1) hu.1 hvval huval
  have hdgrad := tendsto_eLpNorm_sub_pair (fun n => (hvn n).2.1) hv.2.1
    (fun n => (hun n).2.1) hu.2.1 hvgrad hugrad
  have hp := (hv.sub hu).tendsto_eLpNorm_pos_part
    (fun n => (hvn n).sub (hun n)) hdval hdgrad
  constructor
  · have hl := tendsto_eLpNorm_add_pair (fun n => (hun n).1) hu.1
      (fun n => ((hvn n).sub (hun n)).1.pos_part) (hv.sub hu).1.pos_part huval hp.1
    simpa only [max_value_repr] using hl
  · have hl := tendsto_eLpNorm_add_pair (fun n => (hun n).2.1) hu.2.1
      (fun n => ((hvn n).sub (hun n)).pos_part.2.1) (hv.sub hu).pos_part.2.1 hugrad hp.2
    simpa only [max_gradient_repr] using hl

end Torsion

import Torsion.OuterGradientBounds
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Metric outer approximation yields physical dilation sandwiches

A convex domain containing a centered ball absorbs its metric thickening
into an explicit small dilation. This converts ordinary metric outer
approximations into the concrete sandwiches used by the proved weak-gradient
convergence theorem. No smooth approximation existence is asserted here.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Pointwise Topology ENNReal

namespace Torsion

/-- A convex planar set containing a centered ball absorbs a metric
thickening into a quantitative physical dilation. -/
theorem thickening_subset_dilate_of_convex {D : Set Plane} (hD : Convex ℝ D)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hball : ball (0 : Plane) r ⊆ D) :
    thickening δ D ⊆ (1 + δ / r) • D := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
  let s : ℝ := 1 + δ / r
  have hs : 0 < s := by dsimp [s]; positivity
  let w : Plane := (r / δ) • (x - y)
  have hw : w ∈ D := by
    apply hball
    rw [mem_ball, dist_zero_right]
    change ‖(r / δ) • (x - y)‖ < r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hδ)]
    have hh := mul_lt_mul_of_pos_left (show ‖x - y‖ < δ by simpa [dist_eq_norm] using hxy)
      (div_pos hr hδ)
    simpa only [div_mul_cancel₀ _ hδ.ne'] using hh
  let a : ℝ := 1 / s
  let b : ℝ := (δ / r) / s
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← add_div]
    exact div_self hs.ne'
  have hp : a • y + b • w ∈ D := hD hy hw ha hb hab
  have hsa : s * a = 1 := by dsimp [a]; field_simp
  have hsb : s * b * (r / δ) = 1 := by
    dsimp [b]
    field_simp
    ring
  refine ⟨a • y + b • w, hp, ?_⟩
  calc
    s • (a • y + b • w) = y + (x - y) := by
      rw [smul_add, smul_smul, hsa, one_smul]
      change y + s • (b • ((r / δ) • (x - y))) = _
      rw [smul_smul, smul_smul, hsb, one_smul]
    _ = x := by abel

/-- Actual weak torsion gradients converge under arbitrary metric outer
approximations of a convex domain containing a centered ball. Monotonicity,
smoothness and boundary regularity are not needed for this limiting step. -/
theorem DirichletTheory.tendsto_gradient_of_metric_outer (T : DirichletTheory)
    (D : ConvexDomain) (E : ℕ → ConvexDomain)
    {r : ℝ} (hr : 0 < r) (hball : ball (0 : Plane) r ⊆ D.carrier)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hDE : ∀ n, D.carrier ⊆ (E n).carrier)
    (hED : ∀ n, (E n).carrier ⊆ thickening (δ n) D.carrier) :
    Tendsto (fun n => eLpNorm (fun x => (T.solution (E n)).weakGradient x -
      (T.solution D).weakGradient x) 2 volume) atTop (𝓝 0) := by
  apply (T.solution D).weakEquation.tendsto_eLpNorm_gradient_of_outer_dilation
    (fun n => (T.solution (E n)).weakEquation) D.isOpen (fun n => (E n).isOpen)
    (fun n => 1 + δ n / r)
  · intro n
    exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (hδ n).le hr.le)
  · simpa using tendsto_const_nhds.add (hδlim.div_const r)
  · exact hDE
  · intro n
    exact (hED n).trans (thickening_subset_dilate_of_convex D.convex hr (hδ n) hball)

/-- Any area-normalized interior-gradient comparison on metric outer
approximants passes to the original convex domain. -/
theorem DirichletTheory.G_area_bound_of_metric_outer (T : DirichletTheory)
    (D : ConvexDomain) (E : ℕ → ConvexDomain)
    {r : ℝ} (hr : 0 < r) (hball : ball (0 : Plane) r ⊆ D.carrier)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hDE : ∀ n, D.carrier ⊆ (E n).carrier)
    (hED : ∀ n, (E n).carrier ⊆ thickening (δ n) D.carrier) (c : ℝ)
    (hbound : ∀ n, T.G (E n) ≤ ENNReal.ofReal (c * Real.sqrt (E n).area)) :
    T.G D ≤ ENNReal.ofReal (c * Real.sqrt D.area) := by
  apply T.G_area_bound_of_outer_dilation D E (fun n => 1 + δ n / r)
    (fun n => add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (hδ n).le hr.le)) ?_ hDE ?_ c hbound
  · simpa using tendsto_const_nhds.add (hδlim.div_const r)
  · intro n
    exact (hED n).trans (thickening_subset_dilate_of_convex D.convex hr (hδ n) hball)

end Torsion

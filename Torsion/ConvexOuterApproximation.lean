import Torsion.ConvexOuterDilation
import Torsion.TorsionTranslation

/-!
# Outer approximation limits for every bounded convex planar domain

An interior point supplies an inner ball. Translation places its center at
zero, where metric approximation yields a physical dilation sandwich. The
actual weak torsion gradients, areas and gradient-supremum estimates then
pass to the original domain. This removes all boundary trace and Rellich
requirements from the outer approximation limit. Existence of a desired
smooth approximating class, and the comparison estimate on that class, are
not claimed in this module.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Pointwise Topology ENNReal

namespace Torsion

private theorem centered_ball_translate (D : ConvexDomain) {a : Plane} {r : ℝ}
    (hball : ball a r ⊆ D.carrier) : ball (0 : Plane) r ⊆ (D.translate (-a)).carrier := by
  intro x hx
  rw [ConvexDomain.mem_translate, sub_neg_eq_add]
  apply hball
  simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx

private theorem translate_metric_outer {D E : ConvexDomain} {a : Plane} {δ : ℝ}
    (hED : E.carrier ⊆ thickening δ D.carrier) :
    (E.translate (-a)).carrier ⊆ thickening δ (D.translate (-a)).carrier := by
  intro x hx
  have hxE : x + a ∈ E.carrier := by simpa using hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp (hED hxE)
  apply mem_thickening_iff.mpr
  refine ⟨y - a, ?_, ?_⟩
  · simpa using hy
  · calc
      dist x (y - a) = dist (x + a) ((y - a) + a) := (dist_add_right _ _ _).symm
      _ = dist (x + a) y := by rw [sub_add_cancel]
      _ < δ := hxy

/-- Actual global weak torsion gradients converge strongly in L² for every
convex domain under metric outer approximations, without a centered-domain
restriction, nesting, boundary regularity or an assumed trace theorem. -/
theorem DirichletTheory.tendsto_gradient_of_outer_approximation (T : DirichletTheory)
    (D : ConvexDomain) (E : ℕ → ConvexDomain)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hDE : ∀ n, D.carrier ⊆ (E n).carrier)
    (hED : ∀ n, (E n).carrier ⊆ thickening (δ n) D.carrier) :
    Tendsto (fun n => eLpNorm (fun x => (T.solution (E n)).weakGradient x -
      (T.solution D).weakGradient x) 2 volume) atTop (𝓝 0) := by
  obtain ⟨a, ha⟩ := D.nonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp D.isOpen a ha
  have hlim := T.tendsto_gradient_of_metric_outer (D.translate (-a))
    (fun n => (E n).translate (-a)) hr (centered_ball_translate D hball)
    δ hδ hδlim (fun n x hx => hDE n hx)
    (fun n => translate_metric_outer (hED n))
  simpa only [T.eLpNorm_gradient_sub_translate] using hlim

/-- The actual zero-extended weak torsion values also converge strongly in
L² under the same outer approximations. A fixed containing thickening and
the proved bounded-domain Poincaré inequality transfer gradient convergence
to value convergence. -/
theorem DirichletTheory.tendsto_value_of_outer_approximation (T : DirichletTheory)
    (D : ConvexDomain) (E : ℕ → ConvexDomain)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hDE : ∀ n, D.carrier ⊆ (E n).carrier)
    (hED : ∀ n, (E n).carrier ⊆ thickening (δ n) D.carrier) :
    Tendsto (fun n => eLpNorm (fun x => (T.solution (E n)).value x -
      (T.solution D).value x) 2 volume) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hδlim.bddAbove_range
  let B : Set Plane := thickening M D.carrier
  have hEB (n : ℕ) : (E n).carrier ⊆ B :=
    (hED n).trans (thickening_mono (hM (mem_range_self n)) D.carrier)
  have hDB : D.carrier ⊆ B := (hDE 0).trans (hEB 0)
  obtain ⟨K, _, hP⟩ := exists_poincare_constant_of_bounded
    (show Bornology.IsBounded B from D.bounded.thickening)
  have hgrad := T.tendsto_gradient_of_outer_approximation D E δ hδ hδlim hDE hED
  have hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) hgrad
    (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le _)
  intro n
  exact hP _ _ (((T.solution (E n)).weakEquation.1.mono (hEB n)).sub
    ((T.solution D).weakEquation.1.mono hDB))

/-- Full simultaneous global H¹ convergence, stated in the original two
L² coordinates of the actual weak Dirichlet graph. -/
theorem DirichletTheory.tendsto_of_outer_approximation (T : DirichletTheory)
    (D : ConvexDomain) (E : ℕ → ConvexDomain)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hDE : ∀ n, D.carrier ⊆ (E n).carrier)
    (hED : ∀ n, (E n).carrier ⊆ thickening (δ n) D.carrier) :
    Tendsto (fun n => eLpNorm (fun x => (T.solution (E n)).value x -
      (T.solution D).value x) 2 volume) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun x => (T.solution (E n)).weakGradient x -
      (T.solution D).weakGradient x) 2 volume) atTop (𝓝 0) :=
  ⟨T.tendsto_value_of_outer_approximation D E δ hδ hδlim hDE hED,
    T.tendsto_gradient_of_outer_approximation D E δ hδ hδlim hDE hED⟩

/-- Actual Euclidean area converges for arbitrary convex metric outer
approximations. The approximants need not form a monotone sequence. -/
theorem ConvexDomain.area_tendsto_of_outer_approximation
    (D : ConvexDomain) (E : ℕ → ConvexDomain)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hDE : ∀ n, D.carrier ⊆ (E n).carrier)
    (hED : ∀ n, (E n).carrier ⊆ thickening (δ n) D.carrier) :
    Tendsto (fun n => (E n).area) atTop (𝓝 D.area) := by
  obtain ⟨a, ha⟩ := D.nonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp D.isOpen a ha
  have hball₀ := centered_ball_translate D hball
  have hlim := (D.translate (-a)).area_tendsto_of_outer_dilation
    (fun n => (E n).translate (-a)) (fun n => 1 + δ n / r)
    (fun n => add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (hδ n).le hr.le))
    (by simpa using tendsto_const_nhds.add (hδlim.div_const r))
    (fun n x hx => hDE n hx)
    (fun n => (translate_metric_outer (hED n)).trans
      (thickening_subset_dilate_of_convex (D.translate (-a)).convex hr (hδ n) hball₀))
  simpa only [ConvexDomain.translate_area] using hlim

/-- Uniform area-normalized interior-gradient bounds pass through metric
outer approximations for the entire original convex-domain class. The sharp
comparison on the approximants remains an explicit premise. -/
theorem DirichletTheory.G_area_bound_of_outer_approximation (T : DirichletTheory)
    (D : ConvexDomain) (E : ℕ → ConvexDomain)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hDE : ∀ n, D.carrier ⊆ (E n).carrier)
    (hED : ∀ n, (E n).carrier ⊆ thickening (δ n) D.carrier) (c : ℝ)
    (hbound : ∀ n, T.G (E n) ≤ ENNReal.ofReal (c * Real.sqrt (E n).area)) :
    T.G D ≤ ENNReal.ofReal (c * Real.sqrt D.area) := by
  obtain ⟨a, ha⟩ := D.nonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp D.isOpen a ha
  have h := T.G_area_bound_of_metric_outer (D.translate (-a))
    (fun n => (E n).translate (-a)) hr (centered_ball_translate D hball)
    δ hδ hδlim (fun n x hx => hDE n hx)
    (fun n => translate_metric_outer (hED n)) c
    (fun n => by simpa only [T.G_translate, ConvexDomain.translate_area] using hbound n)
  simpa only [T.G_translate, ConvexDomain.translate_area] using h

end Torsion

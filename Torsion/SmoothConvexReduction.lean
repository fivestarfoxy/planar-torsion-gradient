import Torsion.SmoothConvexOuterApproximation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual smooth approximation and reduction of the universal bound

Smooth strictly convex outer approximants are constructed here for every
original `ConvexDomain`. Their actual Euclidean areas and weak torsion
solutions converge by the proved metric outer approximation theorem. Thus
the universal bound reduces to proving it for regular smooth strictly convex
sublevels; that remaining comparison is stated explicitly and is not
inferred from construction or stationarity of a reference domain.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- An actual smooth strictly convex outer approximation sequence of every
convex domain, including regular defining functions and metric containments. -/
theorem ConvexDomain.exists_smooth_strictConvex_outer_sequence (D : ConvexDomain) :
    ∃ (E : ℕ → ConvexDomain) (F : ℕ → Plane → ℝ) (b : ℕ → ℝ),
      (∀ n, ContDiff ℝ ∞ (F n) ∧ StrictConvexOn ℝ univ (F n) ∧
        StrictConvex ℝ (closure (E n).carrier) ∧
        (∀ x ∈ frontier (E n).carrier, fderiv ℝ (F n) x ≠ 0) ∧
        (E n).carrier = {x | F n x < b n}) ∧
      (∀ n, D.carrier ⊆ (E n).carrier) ∧
      (∀ n, (E n).carrier ⊆ thickening (1 / ((n : ℝ) + 1)) D.carrier) := by
  have hex (n : ℕ) := D.exists_smooth_strictConvex_outer
    (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  choose E F b hFs hFc hEc hreg hE hDE hED using hex
  exact ⟨E, F, b, fun n => ⟨hFs n, hFc n, hEc n, hreg n, hE n⟩, hDE, hED⟩

/-- The constructed smooth outer approximants have convergent actual areas
and simultaneous global L² value and weak-gradient coordinates. -/
theorem DirichletTheory.exists_smooth_strictConvex_approximation (T : DirichletTheory)
    (D : ConvexDomain) :
    ∃ (E : ℕ → ConvexDomain) (F : ℕ → Plane → ℝ) (b : ℕ → ℝ),
      (∀ n, ContDiff ℝ ∞ (F n) ∧ StrictConvexOn ℝ univ (F n) ∧
        StrictConvex ℝ (closure (E n).carrier) ∧
        (∀ x ∈ frontier (E n).carrier, fderiv ℝ (F n) x ≠ 0) ∧
        (E n).carrier = {x | F n x < b n}) ∧
      (∀ n, D.carrier ⊆ (E n).carrier) ∧
      (∀ n, (E n).carrier ⊆ thickening (1 / ((n : ℝ) + 1)) D.carrier) ∧
      Tendsto (fun n => (E n).area) atTop (𝓝 D.area) ∧
      Tendsto (fun n => eLpNorm (fun x => (T.solution (E n)).value x -
        (T.solution D).value x) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun x => (T.solution (E n)).weakGradient x -
        (T.solution D).weakGradient x) 2 volume) atTop (𝓝 0) := by
  obtain ⟨E, F, b, hEF, hDE, hED⟩ := D.exists_smooth_strictConvex_outer_sequence
  have hδ (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hlim := T.tendsto_of_outer_approximation D E (fun n => 1 / ((n : ℝ) + 1))
    hδ tendsto_one_div_add_atTop_nhds_zero_nat hDE hED
  exact ⟨E, F, b, hEF, hDE, hED,
    D.area_tendsto_of_outer_approximation E (fun n => 1 / ((n : ℝ) + 1))
      hδ tendsto_one_div_add_atTop_nhds_zero_nat hDE hED,
    hlim.1, hlim.2⟩

/-- Proving the area-normalized gradient comparison on smooth strictly
convex regular sublevels suffices for the entire original admissible class.
The comparison premise is substantive; only its geometric approximation
and analytic limiting passage are discharged here. -/
theorem DirichletTheory.G_area_bound_of_smooth_strictConvex (T : DirichletTheory)
    (c : ℝ)
    (hbound : ∀ (E : ConvexDomain) (F : Plane → ℝ) (b : ℝ),
      ContDiff ℝ ∞ F → StrictConvex ℝ (closure E.carrier) →
      (∀ x ∈ frontier E.carrier, fderiv ℝ F x ≠ 0) →
      E.carrier = {x | F x < b} →
      T.G E ≤ ENNReal.ofReal (c * Real.sqrt E.area)) (D : ConvexDomain) :
    T.G D ≤ ENNReal.ofReal (c * Real.sqrt D.area) := by
  obtain ⟨E, F, b, hEF, hDE, hED⟩ := D.exists_smooth_strictConvex_outer_sequence
  apply T.G_area_bound_of_outer_approximation D E (fun n => 1 / ((n : ℝ) + 1))
    (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat hDE hED c
  intro n
  exact hbound (E n) (F n) (b n) (hEF n).1 (hEF n).2.2.1
    (hEF n).2.2.2.1 (hEF n).2.2.2.2

end Torsion

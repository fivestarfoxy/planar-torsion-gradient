import Torsion.OuterDomainConvergence
import Torsion.GradientBoundExhaustion

/-!
# Outer approximation and the actual interior gradient supremum

The actual weak torsion gradient and Euclidean area converge under outer
physical dilation sandwiches. Consequently any fixed area-normalized bound
on such approximants passes to the original domain. Constructing suitable
smooth approximants and proving a sharp bound on them remain independent
geometric and analytic obligations.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Pointwise Topology ENNReal

namespace Torsion

/-- Euclidean area convergence under an outer dilation sandwich. No
monotonicity of the approximating sequence is required. -/
theorem ConvexDomain.area_tendsto_of_outer_dilation
    (D : ConvexDomain) (E : ℕ → ConvexDomain)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hslim : Tendsto s atTop (𝓝 1))
    (hDE : ∀ n, D.carrier ⊆ (E n).carrier)
    (hEsD : ∀ n, (E n).carrier ⊆ s n • D.carrier) :
    Tendsto (fun n => (E n).area) atTop (𝓝 D.area) := by
  have hupper : Tendsto (fun n => s n ^ 2 * D.area) atTop (𝓝 D.area) := by
    simpa using (hslim.pow 2).mul_const D.area
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro n
    exact ENNReal.toReal_mono (E n).bounded.measure_lt_top.ne (measure_mono (hDE n))
  · intro n
    have h := ENNReal.toReal_mono
      ((D.dilate (s n) (hs n)).bounded.measure_lt_top (μ := (volume : Measure Plane))).ne
      (measure_mono (μ := (volume : Measure Plane)) (hEsD n))
    change (E n).area ≤ (D.dilate (s n) (hs n)).area at h
    simpa only [ConvexDomain.dilate_area] using h

/-- Bounds on outer approximants pass to the original actual interior weak
gradient norm, using proved strong L² convergence and zero extension. -/
theorem DirichletTheory.G_le_of_outer_dilation (T : DirichletTheory)
    (D : ConvexDomain) (E : ℕ → ConvexDomain)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hslim : Tendsto s atTop (𝓝 1))
    (hDE : ∀ n, D.carrier ⊆ (E n).carrier)
    (hEsD : ∀ n, (E n).carrier ⊆ s n • D.carrier)
    {C : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hC : Tendsto C atTop (𝓝 c))
    (hbound : ∀ n, T.G (E n) ≤ C n) : T.G D ≤ c := by
  rw [DirichletTheory.G, ← (T.solution D).weakEquation.1.eLpNorm_gradient_eq_restrict
    D.isOpen.measurableSet]
  apply eLpNorm_top_le_of_tendsto_two
    (fun n => (T.solution (E n)).weakEquation.1.2.1.1)
    (T.solution D).weakEquation.1.2.1.1
    ((T.solution D).weakEquation.tendsto_eLpNorm_gradient_of_outer_dilation
      (fun n => (T.solution (E n)).weakEquation) D.isOpen (fun n => (E n).isOpen)
      s hs hslim hDE hEsD) hC
  intro n
  rw [(T.solution (E n)).weakEquation.1.eLpNorm_gradient_eq_restrict
    (E n).isOpen.measurableSet]
  exact hbound n

/-- The general-domain limiting step for an area-normalized comparison.
This theorem proves passage of the estimate; the comparison on the outer
approximants is still the displayed substantive premise. -/
theorem DirichletTheory.G_area_bound_of_outer_dilation (T : DirichletTheory)
    (D : ConvexDomain) (E : ℕ → ConvexDomain)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hslim : Tendsto s atTop (𝓝 1))
    (hDE : ∀ n, D.carrier ⊆ (E n).carrier)
    (hEsD : ∀ n, (E n).carrier ⊆ s n • D.carrier) (c : ℝ)
    (hbound : ∀ n, T.G (E n) ≤ ENNReal.ofReal (c * Real.sqrt (E n).area)) :
    T.G D ≤ ENNReal.ofReal (c * Real.sqrt D.area) := by
  apply T.G_le_of_outer_dilation D E s hs hslim hDE hEsD
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul
        (D.area_tendsto_of_outer_dilation E s hs hslim hDE hEsD).sqrt)) hbound

end Torsion

module

public import Torsion.DirichletExhaustion
public import Torsion.SobolevSupport
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Passing actual weak-gradient bounds through increasing domains

The gradients in the original Sobolev graph are zero extended. Strong L²
convergence, already proved for an increasing open-domain exhaustion, passes
uniform essential-supremum bounds to the limit. This supplies the limiting
step for a convex-domain comparison once comparison on an exhausting class
has been established; it does not supply that comparison or an exhaustion
by smooth domains.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion

/-- Zero extension does not change the essential supremum of a genuine
zero-boundary Sobolev gradient. -/
theorem MemH10.eLpNorm_gradient_eq_restrict {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : MemH10 D u g)
    (hD : MeasurableSet D) (p : ℝ≥0∞) :
    eLpNorm g p volume = eLpNorm g p (volume.restrict D) := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hD]
  apply eLpNorm_congr_ae
  have hoff := (ae_restrict_iff' hD.compl).mp hu.gradient_ae_zero_off
  filter_upwards [hoff] with x hx
  by_cases hxd : x ∈ D
  · simp [hxd]
  · simp [hxd, hx hxd]

/-- L² convergence passes varying global L∞ bounds to their limit.
No pointwise regularity or boundary trace is needed. -/
theorem eLpNorm_top_le_of_tendsto_two
    {gₙ : ℕ → Plane → Plane} {g : Plane → Plane}
    (hgn : ∀ n, AEStronglyMeasurable (gₙ n) volume)
    (hg : AEStronglyMeasurable g volume)
    (hconv : Tendsto (fun n => eLpNorm (fun x => gₙ n x - g x) 2 volume)
      atTop (𝓝 0))
    {C : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hC : Tendsto C atTop (𝓝 c))
    (hbound : ∀ n, eLpNorm (gₙ n) ∞ volume ≤ C n) :
    eLpNorm g ∞ volume ≤ c := by
  have hm := tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) hgn hg hconv
  obtain ⟨κ, hκ, hae⟩ := hm.exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂volume, ∀ n, ‖gₙ n x‖ₑ ≤ C n := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [enorm_ae_le_eLpNormEssSup (gₙ n) volume] with x hx
    exact hx.trans (hbound n)
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [hae, hall] with x hx hb
  exact le_of_tendsto_of_tendsto
    ((continuous_enorm.tendsto (g x)).comp hx)
    (hC.comp hκ.tendsto_atTop) (Eventually.of_forall fun n => hb (κ n))

/-- Uniform bounds for actual weak torsion on increasing open domains pass
to the weak torsion of their union, with the original interior norm. -/
theorem IsWeakTorsion.gradient_bound_of_exhaustion
    {D : ℕ → Set Plane} (hmono : Monotone D) (hopen : ∀ n, IsOpen (D n))
    {u : Plane → ℝ} {g : Plane → Plane}
    {uₙ : ℕ → Plane → ℝ} {gₙ : ℕ → Plane → Plane}
    (hu : IsWeakTorsion (⋃ n, D n) u g)
    (hun : ∀ n, IsWeakTorsion (D n) (uₙ n) (gₙ n))
    {C : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hC : Tendsto C atTop (𝓝 c))
    (hbound : ∀ n, eLpNorm (gₙ n) ∞ (volume.restrict (D n)) ≤ C n) :
    eLpNorm g ∞ (volume.restrict (⋃ n, D n)) ≤ c := by
  rw [← hu.1.eLpNorm_gradient_eq_restrict (isOpen_iUnion hopen).measurableSet]
  apply eLpNorm_top_le_of_tendsto_two (fun n => (hun n).1.2.1.1) hu.1.2.1.1
    (hu.tendsto_eLpNorm_gradient_of_exhaustion hmono hopen hun) hC
  intro n
  rw [(hun n).1.eLpNorm_gradient_eq_restrict (hopen n).measurableSet]
  exact hbound n

/-- A concrete Dirichlet theory inherits any convergent family of bounds
along a convex-domain exhaustion. -/
theorem DirichletTheory.G_le_of_exhaustion (T : DirichletTheory)
    (D : ℕ → ConvexDomain) (E : ConvexDomain)
    (hmono : Monotone (fun n => (D n).carrier))
    (hunion : (⋃ n, (D n).carrier) = E.carrier)
    {C : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hC : Tendsto C atTop (𝓝 c))
    (hbound : ∀ n, T.G (D n) ≤ C n) : T.G E ≤ c := by
  have hu : IsWeakTorsion (⋃ n, (D n).carrier)
      (T.solution E).value (T.solution E).weakGradient := by
    rw [hunion]
    exact (T.solution E).weakEquation
  have h := hu.gradient_bound_of_exhaustion hmono (fun n => (D n).isOpen)
    (fun n => (T.solution (D n)).weakEquation) hC hbound
  simpa only [hunion, DirichletTheory.G] using h

/-- Actual Euclidean areas converge along an increasing convex-domain
exhaustion. Boundedness of the limiting domain excludes infinite area. -/
theorem ConvexDomain.area_tendsto_of_exhaustion
    (D : ℕ → ConvexDomain) (E : ConvexDomain)
    (hmono : Monotone (fun n => (D n).carrier))
    (hunion : (⋃ n, (D n).carrier) = E.carrier) :
    Tendsto (fun n => (D n).area) atTop (𝓝 E.area) := by
  have hm := tendsto_measure_iUnion_atTop (μ := (volume : Measure Plane)) hmono
  rw [hunion] at hm
  exact (ENNReal.continuousAt_toReal E.bounded.measure_lt_top.ne).tendsto.comp hm

/-- An area-normalized gradient estimate on the members of any increasing
convex-domain exhaustion passes to its actual limiting domain. This leaves
the sharp comparison on the approximants as an explicit premise. -/
theorem DirichletTheory.G_area_bound_of_exhaustion (T : DirichletTheory)
    (D : ℕ → ConvexDomain) (E : ConvexDomain)
    (hmono : Monotone (fun n => (D n).carrier))
    (hunion : (⋃ n, (D n).carrier) = E.carrier) (c : ℝ)
    (hbound : ∀ n, T.G (D n) ≤ ENNReal.ofReal (c * Real.sqrt (D n).area)) :
    T.G E ≤ ENNReal.ofReal (c * Real.sqrt E.area) := by
  apply T.G_le_of_exhaustion D E hmono hunion
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul ((ConvexDomain.area_tendsto_of_exhaustion D E hmono hunion).sqrt)))
    hbound

end Torsion

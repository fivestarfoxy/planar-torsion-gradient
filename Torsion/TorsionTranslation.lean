module

public import Torsion.WeakReflection.Translation
public import Torsion.GradientBoundExhaustion
public import Torsion.SobolevUniqueness

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Translation covariance of the concrete weak torsion problem

The original simultaneous Sobolev graph approximation, actual weak equation,
Lebesgue area and interior essential gradient norm all commute with physical
translations. These facts allow a convex approximation argument to choose an
interior center without restricting the admissible domain class.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion

namespace ConvexDomain

/-- Physical translation by a fixed complex vector. -/
def translate (D : ConvexDomain) (a : Plane) : ConvexDomain where
  carrier := (fun z : Plane => z - a) ⁻¹' D.carrier
  isOpen := D.isOpen.preimage (continuous_id.sub continuous_const)
  bounded := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp D.bounded
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R + ‖a‖, ?_⟩
    intro x hx
    change x - a ∈ D.carrier at hx
    calc
      ‖x‖ = ‖(x - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - a‖ + ‖a‖ := norm_add_le _ _
      _ ≤ R + ‖a‖ := add_le_add (hR _ hx) le_rfl
  convex := by simpa only [sub_eq_add_neg] using D.convex.translate_preimage_left (-a)
  nonempty := by
    obtain ⟨x, hx⟩ := D.nonempty
    exact ⟨x + a, by simpa using hx⟩

theorem translate_carrier (D : ConvexDomain) (a : Plane) :
    (D.translate a).carrier = (fun z : Plane => z + a) '' D.carrier := by
  ext x
  constructor
  · intro hx
    exact ⟨x - a, hx, sub_add_cancel _ _⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [translate, mem_preimage, add_sub_cancel_right] using hy

@[simp] theorem mem_translate (D : ConvexDomain) (a x : Plane) :
    x ∈ (D.translate a).carrier ↔ x - a ∈ D.carrier := Iff.rfl

/-- Actual Euclidean area is invariant under translation. -/
@[simp] theorem translate_area (D : ConvexDomain) (a : Plane) :
    (D.translate a).area = D.area := by
  unfold area
  change (volume ((fun z : Plane => z - a) ⁻¹' D.carrier)).toReal = _
  rw [(measurePreserving_sub_const a).measure_preimage D.isOpen.measurableSet.nullMeasurableSet]

end ConvexDomain

/-- The actual weak Dirichlet equation is preserved by physical translation,
using the established translation of the simultaneous Sobolev graph. -/
theorem IsWeakTorsion.translatedValue {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g)
    (hD : MeasurableSet D) (a : Plane) :
    IsWeakTorsion ((fun z : Plane => z - a) ⁻¹' D)
      (Torsion.translatedValue a u) (Torsion.translatedValue a g) := by
  refine ⟨hu.1.translatedValue a, ?_⟩
  intro v h hv
  have hback : MemH10 D (fun x => v (x + a)) (fun x => h (x + a)) := by
    have hback₀ := hv.translatedValue (-a)
    have hdom : (fun z : Plane => z - (-a)) ⁻¹'
        ((fun z : Plane => z - a) ⁻¹' D) = D := by
      ext x
      simp
    rw [hdom] at hback₀
    convert hback₀ using 1 <;> funext x <;> simp [Torsion.translatedValue]
  have hweak := hu.2 _ _ hback
  have hmp := (measurePreserving_sub_const a).restrict_preimage hD
  have he := (Homeomorph.subRight a).toMeasurableEquiv.measurableEmbedding
  calc
    (∫ z in (fun z : Plane => z - a) ⁻¹' D,
        inner (𝕜 := ℝ) (Torsion.translatedValue a g z) (h z)) =
        ∫ x in D, inner (𝕜 := ℝ) (g x) (h (x + a)) := by
      convert hmp.integral_comp he (fun x => inner (𝕜 := ℝ) (g x) (h (x + a))) using 1
      simp only [Torsion.translatedValue, sub_add_cancel]
    _ = ∫ x in D, v (x + a) := hweak
    _ = ∫ z in (fun z : Plane => z - a) ⁻¹' D, v z := by
      symm
      convert hmp.integral_comp he (fun x => v (x + a)) using 1
      simp only [sub_add_cancel]

/-- The original interior weak-gradient essential supremum is physically
translation invariant, independently of the selected weak solution. -/
@[simp] theorem DirichletTheory.G_translate (T : DirichletTheory)
    (D : ConvexDomain) (a : Plane) : T.G (D.translate a) = T.G D := by
  have hscaled := (T.solution D).weakEquation.translatedValue D.isOpen.measurableSet a
  have hsame := (T.solution (D.translate a)).weakEquation.gradient_ae_eq hscaled
  unfold DirichletTheory.G
  rw [eLpNorm_congr_ae hsame]
  change eLpNorm (Torsion.translatedValue a (T.solution D).weakGradient) ∞
    (volume.restrict ((fun z : Plane => z - a) ⁻¹' D.carrier)) = _
  rw [← hscaled.1.eLpNorm_gradient_eq_restrict (D.translate a).isOpen.measurableSet,
    eLpNorm_translatedValue,
    (T.solution D).weakEquation.1.eLpNorm_gradient_eq_restrict D.isOpen.measurableSet]

/-- Global gradient differences for the actual selected weak solutions have
the same L² norm after a common physical translation. -/
theorem DirichletTheory.eLpNorm_gradient_sub_translate (T : DirichletTheory)
    (D E : ConvexDomain) (a : Plane) :
    eLpNorm (fun x => (T.solution (E.translate a)).weakGradient x -
      (T.solution (D.translate a)).weakGradient x) 2 volume =
    eLpNorm (fun x => (T.solution E).weakGradient x -
      (T.solution D).weakGradient x) 2 volume := by
  have hD := (T.solution (D.translate a)).weakEquation.gradient_global_ae_eq
    (D.translate a).isOpen.measurableSet
    ((T.solution D).weakEquation.translatedValue D.isOpen.measurableSet a)
  have hE := (T.solution (E.translate a)).weakEquation.gradient_global_ae_eq
    (E.translate a).isOpen.measurableSet
    ((T.solution E).weakEquation.translatedValue E.isOpen.measurableSet a)
  calc
    _ = eLpNorm (Torsion.translatedValue a (fun x =>
        (T.solution E).weakGradient x - (T.solution D).weakGradient x)) 2 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [hD, hE] with x hx hy
      exact congrArg₂ (fun y z : Plane => y - z) hy hx
    _ = _ := eLpNorm_translatedValue _ _ _

end Torsion

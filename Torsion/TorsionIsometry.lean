module

public import Torsion.SobolevIsometry
public import Torsion.GradientBoundExhaustion
public import Torsion.SobolevUniqueness

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Orthogonal covariance of the actual weak torsion problem

All real orthogonal maps preserve the original admissible convex class,
actual weak solutions, Euclidean area and interior essential gradient norm.
The construction uses the simultaneous original H¹₀ graph, rather than an
assumed classical boundary solution.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion
namespace ConvexDomain

/-- Physical pullback of an actual domain by a real orthogonal equivalence. -/
def isometryPreimage (D : ConvexDomain) (e : Plane ≃ₗᵢ[ℝ] Plane) : ConvexDomain where
  carrier := e ⁻¹' D.carrier
  isOpen := D.isOpen.preimage e.continuous
  bounded := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp D.bounded
    exact isBounded_iff_forall_norm_le.mpr ⟨R, fun z hz => by
      simpa only [e.norm_map] using hR (e z) hz⟩
  convex := D.convex.linear_preimage e.toLinearMap
  nonempty := by
    obtain ⟨z, hz⟩ := D.nonempty
    exact ⟨e.symm z, by simpa only [mem_preimage, e.apply_symm_apply] using hz⟩

@[simp] theorem mem_isometryPreimage (D : ConvexDomain) (e : Plane ≃ₗᵢ[ℝ] Plane) (z : Plane) :
    z ∈ (D.isometryPreimage e).carrier ↔ e z ∈ D.carrier := Iff.rfl

@[simp] theorem isometryPreimage_area (D : ConvexDomain) (e : Plane ≃ₗᵢ[ℝ] Plane) :
    (D.isometryPreimage e).area = D.area := by
  unfold area
  change (volume (e ⁻¹' D.carrier)).toReal = _
  rw [e.measurePreserving.measure_preimage D.isOpen.measurableSet.nullMeasurableSet]

end ConvexDomain

/-- The actual weak torsion equation is invariant under all real
orthogonal transformations of the physical plane. -/
theorem IsWeakTorsion.isometry_comp {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : MeasurableSet D) (e : Plane ≃ₗᵢ[ℝ] Plane) :
    IsWeakTorsion (e ⁻¹' D) (fun z => u (e z)) (isometryGradient e g) := by
  refine ⟨hu.1.isometry_comp e, ?_⟩
  intro v h hv
  have hback : MemH10 D (fun z => v (e.symm z)) (fun z => e (h (e.symm z))) := by
    have hh := hv.isometry_comp e.symm
    have hdom : e.symm ⁻¹' (e ⁻¹' D) = D := by
      ext z
      simp only [mem_preimage, e.apply_symm_apply]
    rw [hdom] at hh
    exact hh
  have hweak := hu.2 _ _ hback
  have hmp := e.measurePreserving.restrict_preimage hD
  have he := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  calc
    (∫ z in e ⁻¹' D, inner (𝕜 := ℝ) (isometryGradient e g z) (h z)) =
        ∫ z in e ⁻¹' D, inner (𝕜 := ℝ) (g (e z)) (e (h z)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        simpa only [isometryGradient, e.apply_symm_apply] using
          (e.inner_map_map (e.symm (g (e z))) (h z)).symm)
    _ = ∫ z in D, inner (𝕜 := ℝ) (g z) (e (h (e.symm z))) := by
      convert hmp.integral_comp he (fun z => inner (𝕜 := ℝ) (g z) (e (h (e.symm z)))) using 1
      simp only [e.symm_apply_apply]
    _ = ∫ z in D, v (e.symm z) := hweak
    _ = ∫ z in e ⁻¹' D, v z := by
      symm
      convert hmp.integral_comp he (fun z => v (e.symm z)) using 1
      simp only [e.symm_apply_apply]

/-- The actual interior essential gradient supremum is orthogonally
invariant, independently of the selected representatives of weak torsion. -/
@[simp] theorem DirichletTheory.G_isometryPreimage (T : DirichletTheory)
    (D : ConvexDomain) (e : Plane ≃ₗᵢ[ℝ] Plane) : T.G (D.isometryPreimage e) = T.G D := by
  have hpull := (T.solution D).weakEquation.isometry_comp D.isOpen.measurableSet e
  have hsame := (T.solution (D.isometryPreimage e)).weakEquation.gradient_ae_eq hpull
  unfold DirichletTheory.G
  rw [eLpNorm_congr_ae hsame]
  change eLpNorm (isometryGradient e (T.solution D).weakGradient) ∞
    (volume.restrict (e ⁻¹' D.carrier)) = _
  rw [← hpull.1.eLpNorm_gradient_eq_restrict (D.isometryPreimage e).isOpen.measurableSet,
    eLpNorm_isometryGradient,
    (T.solution D).weakEquation.1.eLpNorm_gradient_eq_restrict D.isOpen.measurableSet]

end Torsion

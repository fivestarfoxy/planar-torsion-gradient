module

public import Torsion.WeakGradient
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Physical orthogonal covariance of the original Sobolev graph -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Pulling back a physical vector field includes its orthogonal action. -/
def isometryGradient (e : Plane ≃ₗᵢ[ℝ] Plane) (g : Plane → Plane) (z : Plane) : Plane :=
  e.symm (g (e z))

theorem eLpNorm_isometry_comp {E : Type*} [NormedAddCommGroup E]
    (e : Plane ≃ₗᵢ[ℝ] Plane) (u : Plane → E) (p : ℝ≥0∞) :
    eLpNorm (fun z => u (e z)) p volume = eLpNorm u p volume := by
  have he := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  change eLpNorm (u ∘ e.toHomeomorph.toMeasurableEquiv) p volume = _
  rw [← he.eLpNorm_map_measure]
  change eLpNorm u p (Measure.map (fun z : Plane => e z) volume) = _
  rw [e.measurePreserving.map_eq]

theorem eLpNorm_isometryGradient (e : Plane ≃ₗᵢ[ℝ] Plane)
    (g : Plane → Plane) (p : ℝ≥0∞) :
    eLpNorm (isometryGradient e g) p volume = eLpNorm g p volume := by
  calc
    _ = eLpNorm (fun z => g (e z)) p volume := by
      by_cases h : AEStronglyMeasurable (fun z => g (e z)) volume
      · exact eLpNorm_congr_norm_ae
          (e.symm.continuous.comp_aestronglyMeasurable h) h
          (ae_of_all _ (fun z => e.symm.norm_map (g (e z))))
      · have hn : ¬ AEStronglyMeasurable (isometryGradient e g) volume := by
          intro hm
          apply h
          simpa only [isometryGradient, Function.comp_apply, e.apply_symm_apply] using
            e.continuous.comp_aestronglyMeasurable hm
        rw [eLpNorm_of_not_aestronglyMeasurable hn, eLpNorm_of_not_aestronglyMeasurable h]
    _ = _ := eLpNorm_isometry_comp e g p

theorem memLp_isometryGradient {g : Plane → Plane} {p : ℝ≥0∞}
    (hg : MemLp g p volume) (e : Plane ≃ₗᵢ[ℝ] Plane) :
    MemLp (isometryGradient e g) p volume := by
  have hcomp := hg.comp_measurePreserving e.measurePreserving
  exact hcomp.of_le (e.symm.continuous.comp_aestronglyMeasurable hcomp.aestronglyMeasurable)
    (ae_of_all _ (fun z => (e.symm.norm_map _).le))

/-- The actual classical gradient transforms by the inverse orthogonal map. -/
theorem gradient_isometry_comp {u : Plane → ℝ} (e : Plane ≃ₗᵢ[ℝ] Plane)
    {z : Plane} (hu : DifferentiableAt ℝ u (e z)) :
    gradient (fun x => u (e x)) z = isometryGradient e (gradient u) z := by
  have hd := hu.hasGradientAt.hasFDerivAt.comp z
    e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hd using 1
  · funext v
    simp only [Function.comp_apply]
  ext v
  change inner (𝕜 := ℝ) (e.symm (gradient u (e z))) v =
    inner (𝕜 := ℝ) (gradient u (e z)) (e v)
  simpa only [e.apply_symm_apply] using
    (e.inner_map_map (e.symm (gradient u (e z))) v).symm

theorem IsTest.isometry_comp {D : Set Plane} {f : Plane → ℝ}
    (hf : IsTest D f) (e : Plane ≃ₗᵢ[ℝ] Plane) :
    IsTest (e ⁻¹' D) (fun z => f (e z)) := by
  refine ⟨hf.1.comp e.toContinuousLinearEquiv.contDiff,
    hf.2.1.comp_homeomorph e.toHomeomorph, ?_⟩
  have hsupp : tsupport (fun z => f (e z)) ⊆ e ⁻¹' tsupport f := by
    apply closure_minimal
    · intro z hz
      exact subset_tsupport f hz
    · exact (isClosed_tsupport f).preimage e.continuous
  exact hsupp.trans (preimage_mono hf.2.2)

/-- The simultaneous original value/gradient graph approximation commutes
with every actual real orthogonal equivalence of the physical plane. -/
theorem MemH10.isometry_comp {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) (e : Plane ≃ₗᵢ[ℝ] Plane) :
    MemH10 (e ⁻¹' D) (fun z => u (e z)) (isometryGradient e g) := by
  obtain ⟨hmu, hmg, f, hf, hv, hg⟩ := hu
  refine ⟨hmu.comp_measurePreserving e.measurePreserving, memLp_isometryGradient hmg e,
    fun n z => f n (e z), fun n => (hf n).isometry_comp e, ?_, ?_⟩
  · convert hv using 1
    funext n
    exact eLpNorm_isometry_comp e (fun z => f n z - u z) 2
  · have heq (n : ℕ) :
        (fun z => gradient (fun x => f n (e x)) z - isometryGradient e g z) =
          isometryGradient e (fun z => gradient (f n) z - g z) := by
      funext z
      rw [gradient_isometry_comp e ((hf n).1.differentiable (by simp) _)]
      exact (e.symm.map_sub _ _).symm
    simpa only [heq, eLpNorm_isometryGradient] using hg

end Torsion

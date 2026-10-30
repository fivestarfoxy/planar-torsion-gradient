module

public import Torsion.MarkedFlux
public import Torsion.BoundaryLowerBound

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Comparing the constructed marked flux with the actual interior norm -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

theorem origin_mem_closure_halfBall {r : ℝ} (hr : 0 < r) :
    (0 : Plane) ∈ closure (upperHalfPlane ∩ Metric.ball 0 r) := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (0 : Plane)) := by
    simpa using ((Complex.continuous_ofReal.mul continuous_const).tendsto (0 : ℝ)).mono_left
      nhdsWithin_le_nhds
  exact mem_closure_of_tendsto ht (eventually_vertical_mem_halfBall hr)

/-- The local smooth representative supplied by marked regularity yields
the genuine lower comparison Q(D)≤G(D). The gradient norm remains the
interior essential supremum of the original weak gradient. -/
theorem torsionFlux_le_eLpNorm_of_localRepresentative
    {D : Set Plane} (hD : IsMarked D) {u v : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) {r : ℝ} (hr : 0 < r)
    (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    (hsub : upperHalfPlane ∩ Metric.ball 0 r ⊆ D)
    (hvalue : u =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 r)] v)
    (hgrad : g =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 r)] gradient v) :
    ENNReal.ofReal (torsionFlux D) ≤ eLpNorm g ∞ (volume.restrict D) := by
  have hq := HasTorsionFlux.of_localRepresentative hu hr hv.continuous.continuousOn
    hvalue hv0 (hv.differentiable (by simp) 0)
  rw [← hq.eq_torsionFlux hD]
  have hU : IsOpen (upperHalfPlane ∩ Metric.ball (0 : Plane) r) :=
    (isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball
  have hg : Continuous (gradient v) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp
      (hv.continuous_fderiv (by simp))
  have hb := boundary_im_le_eLpNorm_top hU hg.continuousOn hg.continuousAt.continuousWithinAt
    (origin_mem_closure_halfBall hr)
  apply hb.trans
  rw [eLpNorm_congr_ae hgrad.symm]
  exact eLpNorm_mono_measure g (Measure.restrict_mono_set volume hsub)

/-- Every marked weak torsion problem satisfies Q(D)≤G(D), with no
representative, regularity or boundary-gradient assumption. -/
theorem torsionFlux_le_eLpNorm {D : Set Plane} (hD : IsMarked D)
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g) :
    ENNReal.ofReal (torsionFlux D) ≤ eLpNorm g ∞ (volume.restrict D) := by
  obtain ⟨r, v, hr, hv, hsub, hv0, hvalue, hgrad⟩ :=
    hD.exists_smooth_torsion_representative hu
  exact torsionFlux_le_eLpNorm_of_localRepresentative hD hu hr hv hv0 hsub hvalue hgrad

theorem DirichletTheory.torsionFlux_le_G (T : DirichletTheory) (D : ConvexDomain)
    (hD : IsMarked D.carrier) : ENNReal.ofReal (torsionFlux D.carrier) ≤ T.G D :=
  torsionFlux_le_eLpNorm hD (T.solution D).weakEquation

end Torsion

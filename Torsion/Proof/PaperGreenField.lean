module

public import Torsion.Proof.PaperRadialGreen
public import Torsion.ClassicalWeakTorsion
public import Torsion.SignedBoundaryAdmission
public import Torsion.ConvexTorsionContinuity
public import Torsion.BoundaryLowerBound

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The second Green field and the actual torsion slope -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal
namespace Torsion
open WeakHarmonicRegularity

/-- The vector field giving Green's second identity for torsion and a test. -/
def secondGreenField (u f : Plane → ℝ) (z : Plane) : Plane :=
  u z • gradient f z - f z • gradient u z

theorem secondGreenField_smooth {u f : Plane → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (secondGreenField u f) :=
  (hu.smul (gradient_contDiff hf)).sub (hf.smul (gradient_contDiff hu))

theorem secondGreenField_divergence {u f : Plane → ℝ} (hu : ContDiff ℝ ∞ u)
    (hf : ContDiff ℝ ∞ f) (z : Plane) :
    Shape.divergence (secondGreenField u f) z = u z * planarLaplacian f z - f z * planarLaplacian u z := by
  have hud := hu.differentiable (by simp) z
  have hfd := hf.differentiable (by simp) z
  have hug := (gradient_contDiff hu).differentiable (by simp) z
  have hfg := (gradient_contDiff hf).differentiable (by simp) z
  have HD := ((hud.hasFDerivAt.smul hfg.hasFDerivAt).sub (hfd.hasFDerivAt.smul hug.hasFDerivAt)).fderiv
  unfold Shape.divergence planarLaplacian planarDivergence
  change fderiv ℝ (u • gradient f - f • gradient u) z = _ at HD
  change ((fderiv ℝ (u • gradient f - f • gradient u) z) 1).re +
    ((fderiv ℝ (u • gradient f - f • gradient u) z) Complex.I).im = _
  rw [HD]
  simp [smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    fderiv_apply_eq_inner_gradient, Complex.inner, -inner_gradient_left, -inner_gradient_right]
  ring

/-- The left unit normal to an oriented tangent; it is inward for the
counterclockwise frame in the divergence theorem. -/
def frameInwardNormal (v : Plane) : Plane := ‖v‖⁻¹ • (Complex.I * v)

def frameInwardSlope (u : Plane → ℝ) (z v : Plane) : ℝ :=
  inner ℝ (gradient u z) (frameInwardNormal v)

theorem frameInwardNormal_norm_le (v : Plane) : ‖frameInwardNormal v‖ ≤ 1 := by
  by_cases hv : v = 0
  · simp [frameInwardNormal, hv]
  · simp [frameInwardNormal, norm_ne_zero_iff.mpr hv]

theorem frameInwardSlope_le_gradient (u : Plane → ℝ) (z v : Plane) :
    frameInwardSlope u z v ≤ ‖gradient u z‖ := by
  apply (real_inner_le_norm _ _).trans
  exact mul_le_of_le_one_right (norm_nonneg _) (frameInwardNormal_norm_le v)

/-- Multiplication by arclength removes the normalization of the normal;
this equality also holds at a stationary parameter value. -/
theorem secondGreenField_boundary (u f : Plane → ℝ) (z v : Plane) (hu : u z = 0) :
    planarCross (secondGreenField u f z) v = f z * frameInwardSlope u z v * ‖v‖ := by
  by_cases hv : v = 0
  · simp [hv, planarCross]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    simp [secondGreenField, hu, planarCross, frameInwardSlope, frameInwardNormal,
      Complex.real_smul, Complex.inner, Complex.mul_re, Complex.mul_im,
      -inner_gradient_left, -inner_gradient_right]
    field_simp

private theorem bounded_indicator_memLp (D : ConvexDomain) {E : Type*} [NormedAddCommGroup E]
    (f : Plane → E) (hf : Continuous f) : MemLp (D.carrier.indicator f) 2 volume := by
  rw [memLp_indicator_iff_restrict D.isOpen.measurableSet]
  have : IsFiniteMeasure (volume.restrict D.carrier) := ⟨by simpa using D.bounded.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := D.bounded.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with z hz
  exact hC _ (subset_closure hz)

/-- A smooth classical solution with zero boundary values gives the actual
exterior-zero pair in the project's weak Dirichlet space. -/
theorem smooth_torsion_isWeakTorsion (D : ConvexDomain) {u : Plane → ℝ} (hu : ContDiff ℝ ∞ u)
    (hb : ∀ z ∈ frontier D.carrier, u z = 0) (hpoisson : ∀ z ∈ D.carrier, planarLaplacian u z = -1) :
    IsWeakTorsion D.carrier (D.carrier.indicator u) (D.carrier.indicator (gradient u)) := by
  have hc := continuous_indicator hb hu.continuous.continuousOn
  have hn {z : Plane} (hz : z ∈ D.carrier) : D.carrier.indicator u =ᶠ[𝓝 z] u := by
    filter_upwards [D.isOpen.mem_nhds hz] with x hx
    exact indicator_of_mem hx u
  have hs : ContDiffOn ℝ ∞ (D.carrier.indicator u) D.carrier := fun z hz =>
    (hu.contDiffAt.congr_of_eventuallyEq (hn hz)).contDiffWithinAt
  have hg (z : Plane) (hz : z ∈ D.carrier) :
      D.carrier.indicator (gradient u) z = gradient (D.carrier.indicator u) z := by
    rw [indicator_of_mem hz, (hn hz).gradient_eq]
  have hm := BoundaryAdmission.memH10_of_smooth_zero_extension D.isOpen D.bounded hc hs
    (fun _ hz => indicator_of_notMem hz _) hg (fun _ hz => indicator_of_notMem hz _)
    (bounded_indicator_memLp D _ hu.continuous) (bounded_indicator_memLp D _ (gradient_contDiff hu).continuous)
  apply isWeakTorsion_of_classical_poisson D.isOpen D.bounded hm hs
  · filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with z hz
    exact hg z hz
  · intro z hz
    unfold planarLaplacian planarDivergence
    rw [(hn hz).gradient.fderiv_eq]
    exact hpoisson z hz

theorem frameInwardSlope_le_G (T : DirichletTheory) (D : ConvexDomain) {u : Plane → ℝ}
    (hu : ContDiff ℝ ∞ u)
    (hweak : IsWeakTorsion D.carrier (D.carrier.indicator u) (D.carrier.indicator (gradient u)))
    {z : Plane} (hz : z ∈ closure D.carrier) (v : Plane) :
    frameInwardSlope u z v ≤ (T.G D).toReal := by
  have hgc := (gradient_contDiff hu).continuous
  have hf := boundary_enorm_le_eLpNorm_top D.isOpen hgc.continuousOn hgc.continuousWithinAt hz
  have he := (T.solution D).weakEquation.gradient_ae_eq hweak
  have hi : D.carrier.indicator (gradient u) =ᵐ[volume.restrict D.carrier] gradient u := by
    filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with x hx
    exact indicator_of_mem hx _
  have heq : T.G D = eLpNorm (gradient u) ∞ (volume.restrict D.carrier) := eLpNorm_congr_ae (he.trans hi)
  rw [← heq] at hf
  exact (frameInwardSlope_le_gradient u z v).trans (by simpa using ENNReal.toReal_mono (T.G_lt_top D).ne hf)

end Torsion

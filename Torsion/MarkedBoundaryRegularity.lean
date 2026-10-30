module

public import Torsion.WeakReflection.Poisson
public import Torsion.WeakHarmonicWeyl.Representative
public import Torsion.MarkedFluxComparison
public import Torsion.HilbertDirichlet

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Passing actual reflected representatives to the marked boundary

Oddness of an a.e. harmonic representative becomes pointwise oddness for a
continuous representative on the full ball. In particular the representative
vanishes at the marked point. Subtracting the actual quadratic correction
therefore constructs the original torsion flux once local Weyl regularity
has supplied that representative.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Continuity upgrades the actual odd a.e. class to pointwise oddness on
the whole ball, including its flat diameter. -/
theorem antisymmetric_of_continuous_ae_odd_on_ball
    {w v : Plane → ℝ} {r : ℝ}
    (hv : ContinuousOn v (Metric.ball (0 : Plane) r))
    (hAE : w =ᵐ[volume.restrict (Metric.ball 0 r)] v)
    (hodd : ∀ z, w (star z) = -w z) :
    ∀ z ∈ Metric.ball (0 : Plane) r, v (star z) = -v z := by
  have hconj : MapsTo (star : Plane → Plane) (Metric.ball 0 r) (Metric.ball 0 r) := by
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right, norm_star] using hz
  have hvref : ContinuousOn (fun z => v (star z)) (Metric.ball 0 r) :=
    hv.comp Complex.continuous_conj.continuousOn hconj
  have hglobal : ∀ᵐ z ∂volume, z ∈ Metric.ball (0 : Plane) r → w z = v z :=
    (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hAE
  have hglobalRef := measurePreserving_conjugation.quasiMeasurePreserving.ae hglobal
  have hpoint : (fun z => v (star z)) =ᵐ[volume.restrict (Metric.ball 0 r)] (fun z => -v z) := by
    apply (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr
    filter_upwards [hglobal, hglobalRef] with z hz hzRef
    intro hzB
    rw [← hzRef (hconj hzB), hodd z, hz hzB]
  exact Measure.eqOn_open_of_ae_eq hpoint Metric.isOpen_ball hvref hv.neg

theorem zero_at_origin_of_continuous_ae_odd_on_ball
    {w v : Plane → ℝ} {r : ℝ} (hr : 0 < r)
    (hv : ContinuousOn v (Metric.ball (0 : Plane) r))
    (hAE : w =ᵐ[volume.restrict (Metric.ball 0 r)] v)
    (hodd : ∀ z, w (star z) = -w z) : v 0 = 0 := by
  have heq := antisymmetric_of_continuous_ae_odd_on_ball hv hAE hodd 0 (Metric.mem_ball_self hr)
  simp only [star_zero] at heq
  linarith

/-- The actual odd harmonic correction, when identified with one smooth
representative on a full ball, supplies the original marked torsion flux.
The representative automatically vanishes at the flat marked point. -/
theorem HasTorsionFlux.of_odd_smoothRepresentative
    {D : Set Plane} {u w v : Plane → ℝ} {g : Plane → Plane} {r : ℝ}
    (hu : IsWeakTorsion D u g) (hr : 0 < r) (hv : ContDiff ℝ ∞ v)
    (hwAE : w =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 r)]
      fun z => u z + quadraticIm z)
    (hAE : w =ᵐ[volume.restrict (Metric.ball 0 r)] v)
    (hodd : ∀ z, w (star z) = -w z) : HasTorsionFlux D (gradient v 0).im := by
  have hv0 := zero_at_origin_of_continuous_ae_odd_on_ball hr hv.continuous.continuousOn hAE hodd
  let U : Plane → ℝ := fun z => v z - quadraticIm z
  have hU : ContDiff ℝ ∞ U := hv.sub quadraticIm_contDiff
  have hUAE : u =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 r)] U := by
    have hsmall := ae_restrict_of_ae_restrict_of_subset
      (inter_subset_right : upperHalfPlane ∩ Metric.ball (0 : Plane) r ⊆ Metric.ball 0 r) hAE
    filter_upwards [hwAE, hsmall] with z hz hwz
    dsimp [U]
    linarith
  have hU0 : U 0 = 0 := by simp [U, hv0, quadraticIm]
  have hflux := HasTorsionFlux.of_localRepresentative hu hr
    hU.continuous.continuousOn hUAE hU0 (hU.differentiable (by simp) 0)
  have hgrad : gradient U 0 = gradient v 0 := by
    change (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ (v - quadraticIm) 0) = _
    rw [fderiv_sub (hv.differentiable (by simp) 0)
      (quadraticIm_contDiff.differentiable (by simp) 0), map_sub]
    change gradient v 0 - gradient quadraticIm 0 = gradient v 0
    rw [gradient_quadraticIm]
    simp
  simpa only [hgrad] using hflux

/-- Full local marked regularity for the actual weak torsion pair. The
constructed globally smooth function represents both value and gradient in
an actual marked half-ball contained in the original domain, and vanishes
at its marked flat point. -/
theorem IsMarked.exists_smooth_torsion_representative {D : Set Plane}
    (hD : IsMarked D) {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) :
    ∃ (r : ℝ) (v : Plane → ℝ), 0 < r ∧ ContDiff ℝ ∞ v ∧
      upperHalfPlane ∩ Metric.ball (0 : Plane) r ⊆ D ∧ v 0 = 0 ∧
      (u =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 r)] v) ∧
      (g =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 r)] gradient v) := by
  obtain ⟨R, hR, hflat⟩ := hD.2.2.2
  have hHD : upperHalfPlane ∩ Metric.ball (0 : Plane) R ⊆ D := by
    intro z hz
    rw [← hflat] at hz
    exact hz.1
  obtain ⟨w, h, hmem, hw, hwVal, hwGrad, hodd⟩ :=
    hu.exists_odd_harmonic_extension_with_gradient hD.2.2.1 R hHD
  let s : ℝ := R / 8
  have hs : 0 < s := by dsimp [s]; positivity
  have hball : Metric.ball (0 : Plane) (4 * s) ⊆ Metric.ball 0 R := by
    apply Metric.ball_subset_ball
    dsimp [s]
    linarith
  obtain ⟨v, hv, hAE, hG⟩ := hw.exists_smoothRepresentative_on_ball hmem hs hball
  have hsmall : upperHalfPlane ∩ Metric.ball (0 : Plane) (s / 2) ⊆
      upperHalfPlane ∩ Metric.ball 0 R := by
    apply inter_subset_inter_right
    apply Metric.ball_subset_ball
    dsimp [s]
    linarith
  have hv0 : v 0 = 0 := zero_at_origin_of_continuous_ae_odd_on_ball
    (half_pos hs) hv.continuous.continuousOn hAE hodd
  let V : Plane → ℝ := fun z => v z - quadraticIm z
  have hV : ContDiff ℝ ∞ V := hv.sub quadraticIm_contDiff
  have hVG (z : Plane) : gradient V z = gradient v z - gradient quadraticIm z := by
    unfold gradient
    change (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ (v - quadraticIm) z) = _
    rw [fderiv_sub (hv.differentiable (by simp) z)
      (quadraticIm_contDiff.differentiable (by simp) z), map_sub]
  have hAEsmall := ae_restrict_of_ae_restrict_of_subset
    (inter_subset_right : upperHalfPlane ∩ Metric.ball (0 : Plane) (s / 2) ⊆
      Metric.ball 0 (s / 2)) hAE
  have hGsmall := ae_restrict_of_ae_restrict_of_subset
    (inter_subset_right : upperHalfPlane ∩ Metric.ball (0 : Plane) (s / 2) ⊆
      Metric.ball 0 (s / 2)) hG
  refine ⟨s / 2, V, half_pos hs, hV, hsmall.trans hHD, ?_, ?_, ?_⟩
  · simp [V, hv0, quadraticIm]
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsmall hwVal, hAEsmall] with z hz hwz
    dsimp [V]
    linarith
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsmall hwGrad, hGsmall] with z hz hwz
    rw [hVG, ← hwz, hz, add_sub_cancel_right]

/-- Every actual marked weak torsion problem has a finite genuine inward
flux. Local smoothness is constructed using the weak odd reflection and
the ordinary interior fixed-kernel Weyl argument. -/
theorem IsMarked.exists_torsionFlux {D : Set Plane} (hD : IsMarked D)
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g) :
    ∃ q : ℝ, HasTorsionFlux D q := by
  obtain ⟨R, w, h, hR, hmem, hw, hwAE, hodd⟩ :=
    hD.exists_odd_harmonic_torsion_extension hu
  let s : ℝ := R / 8
  have hs : 0 < s := by dsimp [s]; positivity
  have hball : Metric.ball (0 : Plane) (4 * s) ⊆ Metric.ball 0 R := by
    apply Metric.ball_subset_ball
    dsimp [s]
    linarith
  obtain ⟨v, hv, hAE, hG⟩ := hw.exists_smoothRepresentative_on_ball hmem hs hball
  have hsmall : upperHalfPlane ∩ Metric.ball (0 : Plane) (s / 2) ⊆
      upperHalfPlane ∩ Metric.ball 0 R := by
    apply inter_subset_inter_right
    apply Metric.ball_subset_ball
    dsimp [s]
    linarith
  exact ⟨(gradient v 0).im,
    HasTorsionFlux.of_odd_smoothRepresentative hu (half_pos hs) hv
      (ae_restrict_of_ae_restrict_of_subset hsmall hwAE) hAE hodd⟩

/-- The previously explicit marked-flux existence obligation is discharged
for every marked domain by actual weak existence and boundary regularity. -/
theorem markedFluxExistence_proved : MarkedFluxExistence := by
  intro D hD
  obtain ⟨u⟩ := HilbertDirichlet.exists_dirichletSolution_of_bounded hD.1.measurableSet hD.2.1
  exact hD.exists_torsionFlux u.weakEquation

end Torsion

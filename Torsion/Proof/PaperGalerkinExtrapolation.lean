module

public import Torsion.MarkedBoundaryRegularity
public import Torsion.MarkedFlux
public import Torsion.HarmonicNormalTaylor

/-! # Even normal data for the flat-side extrapolation -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Torsion.Galerkin

private theorem normalDerivative_even {v : Plane → ℝ} {r : ℝ} (hv : ContDiff ℝ ∞ v)
    (hodd : ∀ z ∈ ball (0 : Plane) r, v (star z) = -v z) {t : ℝ} (ht : |t| < r) :
    (gradient v (((-t : ℝ) : Plane)*Complex.I)).im =
      (gradient v ((t : Plane)*Complex.I)).im := by
  let f (s : ℝ) := v ((s : Plane)*Complex.I)
  have hd : Differentiable ℝ f :=
    (hv.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)).differentiable (by simp)
  have he : (fun s : ℝ => f (-s)) =ᶠ[𝓝 t] fun s => -f s := by
    filter_upwards [continuous_abs.continuousAt.eventually_lt continuousAt_const ht] with s hs
    have hz : (s:Plane)*Complex.I ∈ ball (0:Plane) r := by
      simpa [Metric.mem_ball, Complex.norm_real, Real.norm_eq_abs] using hs
    simpa [f, Complex.star_def] using hodd _ hz
  have h₁ : HasDerivAt (fun s : ℝ => f (-s)) (deriv f (-t) * (-1)) t :=
    (hd (-t)).hasDerivAt.comp t (hasDerivAt_id t).neg
  have h₂ : HasDerivAt (fun s : ℝ => -f s) (-deriv f t) t := (hd t).hasDerivAt.neg
  have h := (h₁.congr_of_eventuallyEq he.symm).unique h₂
  rw [← normalLine_deriv hv, ← normalLine_deriv hv]
  change deriv f (-t) = deriv f t
  linarith

/-- On every actual marked torsion problem, the interior corrected normal
slope extends smoothly and evenly across the flat side. Its value at zero
is the physical torsion flux used by the numerical fit. -/
theorem exists_evenCorrectedSlope {D : Set Plane} (hD : IsMarked D)
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g) :
    ∃ (r : ℝ) (V : Plane → ℝ) (q : ℝ → ℝ), 0 < r ∧ ContDiff ℝ ∞ V ∧
      (u =ᵐ[volume.restrict (upperHalfPlane ∩ ball (0 : Plane) r)] V) ∧
      ContDiff ℝ ∞ q ∧ q 0 = torsionFlux D ∧
      (∀ t, |t| < r → q (-t) = q t) ∧
      (∀ t, q t = (gradient V ((t:Plane)*Complex.I)).im + t) := by
  obtain ⟨R,w,h,hR,hm,hw,hval,hodd⟩ := hD.exists_odd_harmonic_torsion_extension hu
  let s := R / 8
  have hs : 0 < s := by dsimp [s]; positivity
  have hb : ball (0:Plane) (4*s) ⊆ ball 0 R :=
    ball_subset_ball (by dsimp [s]; linarith)
  obtain ⟨v,hv,hAE,_⟩ := hw.exists_smoothRepresentative_on_ball hm hs hb
  have hsub : upperHalfPlane ∩ ball (0:Plane) (s/2) ⊆ upperHalfPlane ∩ ball 0 R :=
    inter_subset_inter_right _ (ball_subset_ball (by dsimp [s]; linarith))
  have hwval := ae_restrict_of_ae_restrict_of_subset hsub hval
  let V := fun z => v z - quadraticIm z
  let q := fun t : ℝ => (gradient v ((t:Plane)*Complex.I)).im
  have hV : ContDiff ℝ ∞ V := hv.sub quadraticIm_contDiff
  have hVG (z : Plane) : gradient V z = gradient v z - gradient quadraticIm z := by
    unfold gradient
    change (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ (v - quadraticIm) z) = _
    rw [fderiv_sub (hv.differentiable (by simp) z)
      (quadraticIm_contDiff.differentiable (by simp) z), map_sub]
  refine ⟨s/2,V,q,half_pos hs,hV,?_,?_,?_,?_,?_⟩
  · filter_upwards [hwval, ae_restrict_of_ae_restrict_of_subset inter_subset_right hAE] with z hz hvz
    dsimp [V]
    linarith
  · exact Complex.imCLM.contDiff.comp ((WeakHarmonicRegularity.gradient_contDiff hv).comp
        (Complex.ofRealCLM.contDiff.mul contDiff_const))
  · have hflux := HasTorsionFlux.of_odd_smoothRepresentative hu (half_pos hs) hv hwval hAE hodd
    simpa [q] using hflux.eq_torsionFlux hD
  · intro t ht
    exact normalDerivative_even hv (antisymmetric_of_continuous_ae_odd_on_ball
      hv.continuous.continuousOn hAE hodd) ht
  · intro t
    simp [q, hVG, gradient_quadraticIm, Complex.mul_im]

end Torsion.Galerkin

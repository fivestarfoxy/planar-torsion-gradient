module

public import Torsion.Proof.PaperGreenField
public import Torsion.Proof.PaperSmoothFrame

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Green's identity and the Hermite–Hadamard torsion bound -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace Torsion
open WeakHarmonicRegularity

/-- The positive radial endpoint is a genuine boundary point, also at
the angular seam. -/
theorem radialFrameCurve_mem_frontier (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ)) :
    MapsTo (radialFrameCurve c R) (Icc (-Real.pi) Real.pi) (frontier D.carrier) := by
  have h : MapsTo (radialFrameCurve c R) (Ioo (-Real.pi) Real.pi) (frontier D.carrier) := by
    intro θ hθ
    rw [D.isOpen.frontier_eq]
    refine ⟨?_, fun hz => (lt_irrefl _) ((hmem θ hθ _ (hpos θ)).mp hz)⟩
    let line (r : ℝ) := c + circleMap 0 r θ
    have hc : Continuous line := by dsimp [line, circleMap]; fun_prop
    have inner : MapsTo line (Ioo 0 (R θ)) D.carrier := fun r hr => (hmem θ hθ r hr.1).mpr hr.2
    apply hc.continuousWithinAt.mem_closure _ inner
    rw [closure_Ioo (hpos θ).ne]
    exact ⟨(hpos θ).le, le_rfl⟩
  have hc := h.closure_of_continuousOn (radialFrameCurve_contDiff c hR).continuous.continuousOn
  simpa only [closure_Ioo (neg_lt_self Real.pi_pos).ne, isClosed_frontier.closure_eq] using hc

/-- Density of the inward boundary flux with respect to angular parameter. -/
def radialFluxDensity (γ : ℝ → Plane) (u f : Plane → ℝ) (θ : ℝ) : ℝ :=
  f (γ θ) * frameInwardSlope u (γ θ) (deriv γ θ) * ‖deriv γ θ‖

private theorem laplacian_continuous {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (planarLaplacian f) := by
  have h := (gradient_contDiff hf).continuous_fderiv (by simp)
  exact (Complex.continuous_re.comp (h.clm_apply continuous_const)).add
    (Complex.continuous_im.comp (h.clm_apply continuous_const))

/-- Green's equality for the torsion solution, integrated against any smooth
test function. The boundary uses the true inward derivative and arclength. -/
theorem smoothRadial_secondGreen (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ))
    {u f : Plane → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ z ∈ frontier D.carrier, u z = 0)
    (hpoisson : ∀ z ∈ D.carrier, planarLaplacian u z = -1) :
    (∫ z in D.carrier, f z) =
      (∫ θ in (-Real.pi)..Real.pi, radialFluxDensity (radialFrameCurve c R) u f θ) -
        ∫ z in D.carrier, u z * planarLaplacian f z := by
  let γ := radialFrameCurve c R
  have hid := smooth_radial_frame_divergence D c R hR hpos hend hmem (W := secondGreenField u f)
    ((secondGreenField_smooth hu hf).of_le (m := 1) (by simp))
  have hfront := radialFrameCurve_mem_frontier D c R hR hpos hmem
  have hsub : (∫ z in D.carrier, Shape.divergence (secondGreenField u f) z) =
      (∫ z in D.carrier, u z * planarLaplacian f z) + ∫ z in D.carrier, f z := by
    have hi {g : Plane → ℝ} (hg : Continuous g) : IntegrableOn g D.carrier :=
      (hg.continuousOn.integrableOn_compact D.bounded.isCompact_closure).mono_set subset_closure
    rw [← integral_add (f := fun z => u z * planarLaplacian f z) (g := f)
      (hi (hu.continuous.mul (laplacian_continuous hf))) (hi hf.continuous)]
    apply setIntegral_congr_fun D.isOpen.measurableSet
    intro z hz
    dsimp only
    rw [secondGreenField_divergence hu hf, hpoisson z hz]
    ring
  have hflux : (∫ θ in (-Real.pi)..Real.pi, planarCross (secondGreenField u f (γ θ)) (deriv γ θ)) =
      ∫ θ in (-Real.pi)..Real.pi, radialFluxDensity γ u f θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le (neg_le_self Real.pi_pos.le)] at hθ
    exact secondGreenField_boundary _ _ _ _ (hb _ (hfront hθ))
  rw [hsub] at hid
  change _ = (∫ θ in (-Real.pi)..Real.pi, planarCross (secondGreenField u f (γ θ)) (deriv γ θ)) at hid
  rw [hflux] at hid
  linarith

/-- The total inward slope equals the area under uniform load. -/
theorem smoothRadial_totalFlux (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ))
    {u : Plane → ℝ} (hu : ContDiff ℝ ∞ u) (hb : ∀ z ∈ frontier D.carrier, u z = 0)
    (hpoisson : ∀ z ∈ D.carrier, planarLaplacian u z = -1) :
    (∫ θ in (-Real.pi)..Real.pi, frameInwardSlope u (radialFrameCurve c R θ)
      (deriv (radialFrameCurve c R) θ) * ‖deriv (radialFrameCurve c R) θ‖) = D.area := by
  have h := smoothRadial_secondGreen D c R hR hpos hend hmem hu (f := fun _ => 1) contDiff_const hb hpoisson
  simpa [radialFluxDensity, planarLaplacian, planarDivergence, gradient_const, ConvexDomain.area, Measure.real_def] using h.symm

/-- The domain's weak essential supremum is a valid Hermite–Hadamard
coefficient for smooth subharmonic tests that are nonnegative on its boundary. -/
theorem smoothRadial_hermiteHadamard (T : DirichletTheory) (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ))
    {u f : Plane → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ z ∈ frontier D.carrier, u z = 0)
    (hpoisson : ∀ z ∈ D.carrier, planarLaplacian u z = -1)
    (hsub : ∀ z ∈ D.carrier, 0 ≤ planarLaplacian f z) (hbd : ∀ z ∈ frontier D.carrier, 0 ≤ f z) :
    (∫ z in D.carrier, f z) ≤ (T.G D).toReal *
      ∫ θ in (-Real.pi)..Real.pi, f (radialFrameCurve c R θ) * ‖deriv (radialFrameCurve c R) θ‖ := by
  let γ := radialFrameCurve c R
  have hγ := radialFrameCurve_contDiff c hR
  have hweak := smooth_torsion_isWeakTorsion D hu hb hpoisson
  have hfront := radialFrameCurve_mem_frontier D c R hR hpos hmem
  have hnon : 0 ≤ ∫ z in D.carrier, u z * planarLaplacian f z := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae (hweak.nonneg_ae D.bounded), ae_restrict_mem D.isOpen.measurableSet] with z hzu hz
    rw [indicator_of_mem hz] at hzu
    exact mul_nonneg hzu (hsub z hz)
  have hflux : (∫ θ in (-Real.pi)..Real.pi, radialFluxDensity γ u f θ) ≤ (T.G D).toReal *
      ∫ θ in (-Real.pi)..Real.pi, f (γ θ) * ‖deriv γ θ‖ := by
    rw [← intervalIntegral.integral_const_mul]
    have hc : Continuous (fun t => planarCross (secondGreenField u f (γ t)) (deriv γ t)) :=
      continuous_planarCross ((secondGreenField_smooth hu hf).continuous.comp hγ.continuous) hγ.continuous_deriv_one
    have hspeed := hγ.continuous_deriv_one.norm
    have hfi : IntervalIntegrable (radialFluxDensity γ u f) volume (-Real.pi) Real.pi := by
      apply (hc.intervalIntegrable _ _).congr
      intro t ht
      have ht' : t ∈ Icc (-Real.pi) Real.pi := (uIcc_of_le (neg_le_self Real.pi_pos.le)) ▸ uIoc_subset_uIcc ht
      exact secondGreenField_boundary _ _ _ _ (hb _ (hfront ht'))
    apply intervalIntegral.integral_mono_on (neg_le_self Real.pi_pos.le) hfi
      ((continuous_const.mul ((hf.continuous.comp hγ.continuous).mul hspeed)).intervalIntegrable _ _)
    intro θ hθ
    have hq := frameInwardSlope_le_G T D hu hweak (frontier_subset_closure (hfront hθ)) (deriv γ θ)
    change f (γ θ) * frameInwardSlope u (γ θ) (deriv γ θ) * ‖deriv γ θ‖ ≤
      (T.G D).toReal * (f (γ θ) * ‖deriv γ θ‖)
    rw [← mul_assoc (T.G D).toReal, mul_comm (T.G D).toReal]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (hbd _ (hfront hθ))) (norm_nonneg _)
  rw [smoothRadial_secondGreen D c R hR hpos hend hmem hu hf hb hpoisson]
  exact (sub_le_self _ hnon).trans hflux

end Torsion

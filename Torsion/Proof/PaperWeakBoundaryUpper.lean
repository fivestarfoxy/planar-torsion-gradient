module

public import Torsion.Proof.PaperTorsionContraction
public import Torsion.Proof.PaperRadialHermite

@[expose] public section

/-! # The sharp upper estimate without a boundary regularity hypothesis on torsion -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion
open WeakHarmonicRegularity

private theorem planarCross_le_norm (z w : Plane) : planarCross z w ≤ ‖z‖ * ‖w‖ := by
  have h : planarCross z w = ((star z) * w).im := by simp [planarCross, Complex.mul_im]; ring
  rw [h, ← Complex.norm_conj z, ← norm_mul]
  exact (le_abs_self _).trans (Complex.abs_im_le_norm _)

private theorem greenBoundary_le {u f : Plane → ℝ} {z v : Plane} {B G : ℝ}
    (hu : 0 ≤ u z) (hB : u z ≤ B) (hf : 0 ≤ f z) (hG : ‖gradient u z‖ ≤ G) :
    planarCross (secondGreenField u f z) v ≤
      B * (‖gradient f z‖ * ‖v‖) + G * (f z * ‖v‖) := by
  apply (planarCross_le_norm _ _).trans
  have hb := norm_sub_le (u z • gradient f z) (f z • gradient u z)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu, abs_of_nonneg hf] at hb
  apply (mul_le_mul_of_nonneg_right hb (norm_nonneg v)).trans
  have e1 := mul_le_mul_of_nonneg_right hB (norm_nonneg (gradient f z))
  have e2 := mul_le_mul_of_nonneg_left hG hf
  calc
    _ ≤ (B * ‖gradient f z‖ + f z * G) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (add_le_add e1 e2) (norm_nonneg _)
    _ = _ := by ring

/-- For any smooth radial description of a bounded convex frame, the original
weak-gradient norm bounds the interior integral of every smooth subharmonic
test that is nonnegative on the boundary. Only the radius must be C¹. -/
theorem smoothRadial_weak_hermiteHadamard (T : DirichletTheory) (D : ConvexDomain)
    (c : Plane) (R : ℝ → ℝ) (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ)
    (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ))
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hsub : ∀ z ∈ D.carrier, 0 ≤ planarLaplacian f z) (hbd : ∀ z ∈ frontier D.carrier, 0 ≤ f z) :
    (∫ z in D.carrier, f z) ≤ (T.G D).toReal *
      ∫ θ in (-Real.pi)..Real.pi, f (radialFrameCurve c R θ) * ‖deriv (radialFrameCurve c R) θ‖ := by
  let γ := radialFrameCurve c R
  let G := (T.G D).toReal
  let d := Metric.diam (closure D.carrier)
  let A := ∫ z in D.carrier, f z
  let B := ∫ θ in (-Real.pi)..Real.pi, f (γ θ) * ‖deriv γ θ‖
  let E := ∫ θ in (-Real.pi)..Real.pi, ‖gradient f (γ θ)‖ * ‖deriv γ θ‖
  have hγ := radialFrameCurve_contDiff c hR
  have hfront := radialFrameCurve_mem_frontier D c R hR hpos hmem
  have hcB := (hf.continuous.comp hγ.continuous).mul hγ.continuous_deriv_one.norm
  have hcE := ((gradient_contDiff hf).continuous.norm.comp hγ.continuous).mul hγ.continuous_deriv_one.norm
  have hineq (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
      s^2 * A ≤ (1-s) * (G*d) * E + G * B := by
    obtain ⟨u,hu,hΔ,hbound,hrim⟩ := T.exists_contracted_torsion D hs hs1
    let W := secondGreenField u f
    have hw := secondGreenField_smooth hu hf
    have hd := (hw.continuous_fderiv (by simp))
    have hdiv : Continuous (Shape.divergence W) :=
      (Complex.continuous_re.comp (hd.clm_apply continuous_const)).add
      (Complex.continuous_im.comp (hd.clm_apply continuous_const))
    have hvol : s^2 * A ≤ ∫ z in D.carrier, Shape.divergence W z := by
      rw [show A = ∫ z in D.carrier, f z from rfl, ← integral_const_mul]
      refine setIntegral_mono_on ?_ ?_ D.isOpen.measurableSet ?_
      · exact ((continuous_const.mul hf.continuous).continuousOn.integrableOn_compact
          D.bounded.isCompact_closure).mono_set subset_closure
      · exact (hdiv.continuousOn.integrableOn_compact D.bounded.isCompact_closure).mono_set subset_closure
      · intro z hz
        rw [show W = secondGreenField u f from rfl, secondGreenField_divergence hu hf, hΔ _ hz]
        nlinarith only [mul_nonneg (hbound z (subset_closure hz)).1 (hsub z hz)]
    rw [smooth_radial_frame_divergence D c R hR hpos hend hmem (hw.of_le (by simp))] at hvol
    apply hvol.trans
    have hRHS : ((1-s)*(G*d))*E + G*B = ∫ θ in (-Real.pi)..Real.pi,
        ((1-s)*(G*d))*(‖gradient f (γ θ)‖*‖deriv γ θ‖) + G*(f (γ θ)*‖deriv γ θ‖) := by
      have ie : IntervalIntegrable (fun θ => ((1-s)*(G*d))*(‖gradient f (γ θ)‖*‖deriv γ θ‖)) volume (-Real.pi) Real.pi :=
        ((continuous_const.mul hcE).intervalIntegrable _ _)
      have ib : IntervalIntegrable (fun θ => G*(f (γ θ)*‖deriv γ θ‖)) volume (-Real.pi) Real.pi :=
        ((continuous_const.mul hcB).intervalIntegrable _ _)
      rw [intervalIntegral.integral_add ie ib, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [hRHS]
    apply intervalIntegral.integral_mono_on (neg_le_self Real.pi_pos.le)
      ((continuous_planarCross (hw.continuous.comp hγ.continuous) hγ.continuous_deriv_one).intervalIntegrable _ _)
      (((continuous_const.mul hcE).add (continuous_const.mul hcB)).intervalIntegrable _ _)
    intro θ hθ
    have hp := hfront hθ
    exact greenBoundary_le (hbound _ (frontier_subset_closure hp)).1 (hrim _ hp) (hbd _ hp)
      (hbound _ (frontier_subset_closure hp)).2
  have ht : Tendsto (fun s : ℝ => s^2 * A) (𝓝[<] 1) (𝓝 (1^2 * A)) :=
    ((continuous_id.pow 2).mul continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hv : Tendsto (fun s : ℝ => (1-s)*(G*d)*E+G*B) (𝓝[<] 1) (𝓝 ((1-1)*(G*d)*E+G*B)) :=
    ((((continuous_const.sub continuous_id).mul continuous_const).mul continuous_const).add continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := le_of_tendsto_of_tendsto ht hv (show ∀ᶠ s : ℝ in 𝓝[<] 1,
      s^2*A ≤ (1-s)*(G*d)*E+G*B from by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))] with s hs hsp
    exact hineq s hsp hs)
  simpa using hlim

end Torsion

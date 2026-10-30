module

public import Torsion.CauchyTransformBoundaryExtension

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiation of the actual Cauchy integral for integrable densities

The uniform denominator bound in a ball above the axis allows ordinary
dominated differentiation with an L¹ density. No endpoint continuity of a
weak spectral representative is required.
-/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace Torsion.Spectral

theorem hasDerivAt_cauchy_integral_of_integrable {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc (-1 : ℝ) 1)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun w : ℂ => ∫ s in Icc (-1 : ℝ) 1, f s / (w - (s : ℂ)))
      (∫ s in Icc (-1 : ℝ) 1, -f s / (z - (s : ℂ)) ^ 2) z := by
  let F : ℂ → ℝ → ℂ := fun w s => f s / (w - (s : ℂ))
  let F' : ℂ → ℝ → ℂ := fun w s => -f s / (w - (s : ℂ)) ^ 2
  let bound : ℝ → ℝ := fun s => ‖f s‖ / (z.im / 2) ^ 2
  have hε : 0 < z.im / 2 := by linarith
  have hmeas (w : ℂ) : AEStronglyMeasurable (F w) (volume.restrict (Icc (-1 : ℝ) 1)) := by
    have hk : Continuous (fun s : ℝ => w - (s : ℂ)) :=
      continuous_const.sub Complex.continuous_ofReal
    change AEStronglyMeasurable (fun s : ℝ => f s / (w - (s : ℂ)))
      (volume.restrict (Icc (-1 : ℝ) 1))
    exact (hf.aestronglyMeasurable.div₀ hk.aestronglyMeasurable).congr
      (ae_of_all _ fun s => by simp only [Pi.div_apply])
  have hint : Integrable (F z) (volume.restrict (Icc (-1 : ℝ) 1)) := by
    apply (hf.norm.div_const (z.im / 2)).mono' (hmeas z)
    exact ae_of_all _ fun s => by
      dsimp only [F]
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hε
        (half_im_le_norm_sub_real hz (mem_ball_self hε) s)
  have hmeas' : AEStronglyMeasurable (F' z) (volume.restrict (Icc (-1 : ℝ) 1)) := by
    have hk : Continuous (fun s : ℝ => (z - (s : ℂ)) ^ 2) :=
      (continuous_const.sub Complex.continuous_ofReal).pow 2
    exact (hf.aestronglyMeasurable.neg.div₀ hk.aestronglyMeasurable).congr
      (ae_of_all _ fun s => by simp only [F', Pi.div_apply, Pi.neg_apply])
  have hbound : ∀ᵐ s : ℝ ∂volume.restrict (Icc (-1 : ℝ) 1),
      ∀ w ∈ ball z (z.im / 2), ‖F' w s‖ ≤ bound s := by
    filter_upwards with s w hw
    dsimp only [F', bound]
    rw [norm_div, norm_neg, norm_pow]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hε)
    exact pow_le_pow_left₀ hε.le (half_im_le_norm_sub_real hz hw s) 2
  have hintbound : Integrable bound (volume.restrict (Icc (-1 : ℝ) 1)) :=
    hf.norm.div_const _
  have hdiff : ∀ᵐ s : ℝ ∂volume.restrict (Icc (-1 : ℝ) 1),
      ∀ w ∈ ball z (z.im / 2), HasDerivAt (fun w => F w s) (F' w s) w := by
    filter_upwards with s w hw
    have hd : ‖z - w‖ < z.im / 2 := by
      simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hw
    have him := Complex.im_le_norm (z - w)
    have hwpos : 0 < w.im := by
      simp only [Complex.sub_im] at him
      linarith
    have hne : w - (s : ℂ) ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
      linarith
    simpa [F, F', Pi.div_def] using!
      (hasDerivAt_const w (f s)).div ((hasDerivAt_id w).sub_const (s : ℂ)) hne
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds z hε) (Eventually.of_forall hmeas) hint hmeas' hbound hintbound hdiff).2

theorem hasDerivAt_realCauchy_of_integrable {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (-1 : ℝ) 1)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (realCauchy f)
      ((Real.pi : ℂ)⁻¹ * ∫ s in Icc (-1 : ℝ) 1, (f s : ℂ) / (z - (s : ℂ)) ^ 2) z := by
  have hfc : IntegrableOn (fun s => (f s : ℂ)) (Icc (-1 : ℝ) 1) :=
    Complex.ofRealCLM.integrable_comp hf
  simpa only [realCauchy, neg_div, integral_neg, neg_mul_neg] using!
    (hasDerivAt_cauchy_integral_of_integrable hfc hz).const_mul (-((Real.pi : ℂ)⁻¹))

end Torsion.Spectral

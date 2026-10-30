import Torsion.SpectralPositivity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

/-!
# Holomorphy of the concrete Cauchy transforms

The compactly supported Cauchy transform is differentiated under its actual
Bochner integral. The domination comes from the distance to the real axis;
no holomorphy or derivative property is included among the hypotheses.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace Torsion.Spectral

private theorem sub_ofReal_ne_zero {z : ℂ} (hz : 0 < z.im) (s : ℝ) :
    z - (s : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
  linarith

/-- A common denominator bound on a ball lying above the real axis. -/
theorem half_im_le_norm_sub_real {z w : ℂ} (_hz : 0 < z.im)
    (hw : w ∈ ball z (z.im / 2)) (s : ℝ) :
    z.im / 2 ≤ ‖w - (s : ℂ)‖ := by
  have hd : ‖z - w‖ < z.im / 2 := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hw
  have hi := Complex.im_le_norm (z - w)
  have hs := Complex.im_le_norm (w - (s : ℂ))
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi hs
  linarith

private theorem im_pos_of_mem_half_im_ball {z w : ℂ} (hz : 0 < z.im)
    (hw : w ∈ ball z (z.im / 2)) : 0 < w.im := by
  have hd : ‖z - w‖ < z.im / 2 := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hw
  have hi := Complex.im_le_norm (z - w)
  simp only [Complex.sub_im] at hi
  linarith

private theorem cauchy_kernel_continuousOn {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {z : ℂ} (hz : 0 < z.im) :
    ContinuousOn (fun s : ℝ => f s / (z - (s : ℂ))) (Icc (-1 : ℝ) 1) := by
  exact hf.div (continuous_const.sub Complex.continuous_ofReal).continuousOn
    (fun s _ => sub_ofReal_ne_zero hz s)

/-- The derivative of the compact Cauchy integral in the upper half-plane.
The density only needs to be continuous on its integration interval. -/
theorem hasDerivAt_cauchy_integral {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun w : ℂ => ∫ s in Icc (-1 : ℝ) 1, f s / (w - (s : ℂ)))
      (∫ s in Icc (-1 : ℝ) 1, -f s / (z - (s : ℂ)) ^ 2) z := by
  let F : ℂ → ℝ → ℂ := fun w s => f s / (w - (s : ℂ))
  let F' : ℂ → ℝ → ℂ := fun w s => -f s / (w - (s : ℂ)) ^ 2
  let bound : ℝ → ℝ := fun s => ‖f s‖ / (z.im / 2) ^ 2
  have hε : 0 < z.im / 2 := by linarith
  have hmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (F w) (volume.restrict (Icc (-1 : ℝ) 1)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
    exact (cauchy_kernel_continuousOn hf hw).aestronglyMeasurable measurableSet_Icc
  have hint : Integrable (F z) (volume.restrict (Icc (-1 : ℝ) 1)) :=
    (cauchy_kernel_continuousOn hf hz).integrableOn_Icc
  have hmeas' : AEStronglyMeasurable (F' z) (volume.restrict (Icc (-1 : ℝ) 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Icc
    exact hf.neg.div ((continuous_const.sub Complex.continuous_ofReal).pow 2).continuousOn
      (fun s _ => pow_ne_zero 2 (sub_ofReal_ne_zero hz s))
  have hbound : ∀ᵐ s : ℝ ∂volume.restrict (Icc (-1 : ℝ) 1),
      ∀ w ∈ ball z (z.im / 2), ‖F' w s‖ ≤ bound s := by
    filter_upwards with s w hw
    dsimp [F', bound]
    rw [norm_div, norm_neg, norm_pow]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hε)
    exact pow_le_pow_left₀ hε.le (half_im_le_norm_sub_real hz hw s) 2
  have hintbound : Integrable bound (volume.restrict (Icc (-1 : ℝ) 1)) :=
    hf.integrableOn_Icc.norm.div_const _
  have hdiff : ∀ᵐ s : ℝ ∂volume.restrict (Icc (-1 : ℝ) 1),
      ∀ w ∈ ball z (z.im / 2), HasDerivAt (fun w => F w s) (F' w s) w := by
    filter_upwards with s w hw
    have hne := sub_ofReal_ne_zero (im_pos_of_mem_half_im_ball hz hw) s
    simpa [F, F'] using
      (hasDerivAt_const w (f s)).div ((hasDerivAt_id w).sub_const (s : ℂ)) hne
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hε hmeas hint hmeas' hbound hintbound hdiff).2

/-- Holomorphy of the compact Cauchy integral follows from the proved
derivative formula, rather than being postulated as boundary input. -/
theorem differentiableOn_cauchy_integral {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    DifferentiableOn ℂ
      (fun w : ℂ => ∫ s in Icc (-1 : ℝ) 1, f s / (w - (s : ℂ))) upperHalfPlane := by
  intro z hz
  exact (hasDerivAt_cauchy_integral hf hz).differentiableAt.differentiableWithinAt

/-- The concrete transform (1.4) has the derivative obtained by formally
differentiating its Cauchy kernel. The preceding theorem justifies that step. -/
theorem hasDerivAt_cauchy {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasDerivAt (cauchy φ)
      ((Real.pi : ℂ)⁻¹ *
        ∫ s in Icc (-1 : ℝ) 1, (height φ s : ℂ) / (z - (s : ℂ)) ^ 2) z := by
  have hc : ContinuousOn (fun s : ℝ => (height φ s : ℂ)) (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp (height_continuous hφ)).continuousOn
  simpa only [cauchy, neg_div, integral_neg, neg_mul_neg] using
    (hasDerivAt_cauchy_integral hc hz).const_mul (-((Real.pi : ℂ)⁻¹))

/-- Holomorphy of the concrete transform constructed from the integrated
spectral profile. No eigenfunction equation is needed for this step. -/
theorem cauchy_differentiableOn {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    DifferentiableOn ℂ (cauchy φ) upperHalfPlane := by
  intro z hz
  exact (hasDerivAt_cauchy hφ hz).differentiableAt.differentiableWithinAt

theorem deriv_cauchy_eq {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    deriv (cauchy φ) z = (Real.pi : ℂ)⁻¹ *
      ∫ s in Icc (-1 : ℝ) 1, (height φ s : ℂ) / (z - (s : ℂ)) ^ 2 :=
  (hasDerivAt_cauchy hφ hz).deriv

/-- The same concrete differentiation theorem for the auxiliary transform
(5.3), including its factor `1/(2π)`. -/
theorem hasDerivAt_auxiliary {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasDerivAt (auxiliary φ)
      ((2 * Real.pi : ℂ)⁻¹ *
        ∫ s in Icc (-1 : ℝ) 1, (((height φ s) ^ 2 : ℝ) : ℂ) / (z - (s : ℂ)) ^ 2) z := by
  have hc : ContinuousOn (fun s : ℝ => (((height φ s) ^ 2 : ℝ) : ℂ))
      (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp ((height_continuous hφ).pow 2)).continuousOn
  simpa only [auxiliary, neg_div, integral_neg, neg_mul_neg] using
    (hasDerivAt_cauchy_integral hc hz).const_mul (-((2 * Real.pi : ℂ)⁻¹))

theorem auxiliary_differentiableOn {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    DifferentiableOn ℂ (auxiliary φ) upperHalfPlane := by
  intro z hz
  exact (hasDerivAt_auxiliary hφ hz).differentiableAt.differentiableWithinAt

theorem deriv_auxiliary_eq {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    deriv (auxiliary φ) z = (2 * Real.pi : ℂ)⁻¹ *
      ∫ s in Icc (-1 : ℝ) 1, (((height φ s) ^ 2 : ℝ) : ℂ) / (z - (s : ℂ)) ^ 2 :=
  (hasDerivAt_auxiliary hφ hz).deriv

/-- The defining transforms are analytic in neighborhoods of each interior
point, so their derivatives are holomorphic as used in the defect identity. -/
theorem cauchy_analyticOnNhd {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    AnalyticOnNhd ℂ (cauchy φ) upperHalfPlane :=
  (cauchy_differentiableOn hφ).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_im)

theorem auxiliary_analyticOnNhd {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    AnalyticOnNhd ℂ (auxiliary φ) upperHalfPlane :=
  (auxiliary_differentiableOn hφ).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_im)

theorem cauchy_derivative_analyticOnNhd {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    AnalyticOnNhd ℂ (deriv (cauchy φ)) upperHalfPlane :=
  (cauchy_analyticOnNhd hφ).deriv

theorem auxiliary_derivative_analyticOnNhd {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    AnalyticOnNhd ℂ (deriv (auxiliary φ)) upperHalfPlane :=
  (auxiliary_analyticOnNhd hφ).deriv

end Torsion.Spectral

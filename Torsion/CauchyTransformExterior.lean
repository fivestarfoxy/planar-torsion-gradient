module

public import Torsion.CauchyConformalGeometry.BoundaryGeometry
public import Torsion.CauchyTransformDecay

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The Cauchy integral across the exterior real boundary

Outside the closed support interval the defining integral is holomorphic on
an actual complex neighborhood. The continuous boundary extension agrees
there with that integral, so its real-boundary derivative has the expected
positive-kernel formula.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace Torsion.Spectral

private theorem exterior_norm_sub_lower {z w : ℂ} (hw : w ∈ ball z ((‖z‖ - 1) / 2))
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    (‖z‖ - 1) / 2 ≤ ‖w - (s : ℂ)‖ := by
  have hd : ‖z - w‖ < (‖z‖ - 1) / 2 := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hw
  have hs1 : ‖(s : ℂ)‖ ≤ 1 := by simpa using abs_le.2 hs
  have hzw := norm_sub_norm_le z w
  have hws := norm_sub_norm_le w (s : ℂ)
  linarith

private theorem exterior_sub_ne_zero {z : ℂ} (hz : 1 < ‖z‖)
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) : z - (s : ℂ) ≠ 0 := by
  intro heq
  have heq' : z = (s : ℂ) := sub_eq_zero.mp heq
  have hs1 : ‖(s : ℂ)‖ ≤ 1 := by simpa using abs_le.2 hs
  rw [heq'] at hz
  linarith

private theorem exterior_kernel_continuousOn {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {z : ℂ} (hz : 1 < ‖z‖) :
    ContinuousOn (fun s : ℝ => f s / (z - (s : ℂ))) (Icc (-1 : ℝ) 1) :=
  hf.div (continuous_const.sub Complex.continuous_ofReal).continuousOn
    (fun _ hs => exterior_sub_ne_zero hz hs)

/-- The actual compact Cauchy integral is differentiable beyond its support,
with the same derivative formula as in the half-plane. -/
theorem hasDerivAt_cauchy_integral_exterior {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {z : ℂ} (hz : 1 < ‖z‖) :
    HasDerivAt (fun w : ℂ => ∫ s in Icc (-1 : ℝ) 1, f s / (w - (s : ℂ)))
      (∫ s in Icc (-1 : ℝ) 1, -f s / (z - (s : ℂ)) ^ 2) z := by
  let F : ℂ → ℝ → ℂ := fun w s => f s / (w - (s : ℂ))
  let F' : ℂ → ℝ → ℂ := fun w s => -f s / (w - (s : ℂ)) ^ 2
  let bound : ℝ → ℝ := fun s => ‖f s‖ / ((‖z‖ - 1) / 2) ^ 2
  have hε : 0 < (‖z‖ - 1) / 2 := by linarith
  have hmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (F w) (volume.restrict (Icc (-1 : ℝ) 1)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact (exterior_kernel_continuousOn hf hw).aestronglyMeasurable measurableSet_Icc
  have hint : Integrable (F z) (volume.restrict (Icc (-1 : ℝ) 1)) :=
    (exterior_kernel_continuousOn hf hz).integrableOn_Icc
  have hmeas' : AEStronglyMeasurable (F' z) (volume.restrict (Icc (-1 : ℝ) 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Icc
    exact hf.neg.div ((continuous_const.sub Complex.continuous_ofReal).pow 2).continuousOn
      (fun s hs => pow_ne_zero 2 (exterior_sub_ne_zero hz hs))
  have hbound : ∀ᵐ s : ℝ ∂volume.restrict (Icc (-1 : ℝ) 1),
      ∀ w ∈ ball z ((‖z‖ - 1) / 2), ‖F' w s‖ ≤ bound s := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs w hw
    dsimp [F', bound]
    rw [norm_div, norm_neg, norm_pow]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hε)
    exact pow_le_pow_left₀ hε.le (exterior_norm_sub_lower hw hs) 2
  have hintbound : Integrable bound (volume.restrict (Icc (-1 : ℝ) 1)) :=
    hf.integrableOn_Icc.norm.div_const _
  have hdiff : ∀ᵐ s : ℝ ∂volume.restrict (Icc (-1 : ℝ) 1),
      ∀ w ∈ ball z ((‖z‖ - 1) / 2), HasDerivAt (fun w => F w s) (F' w s) w := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs w hw
    have hne : w - (s : ℂ) ≠ 0 :=
      norm_pos_iff.1 (hε.trans_le (exterior_norm_sub_lower hw hs))
    simpa [F, F'] using!
      (hasDerivAt_const w (f s)).div ((hasDerivAt_id w).sub_const (s : ℂ)) hne
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds z hε) hmeas hint hmeas' hbound hintbound hdiff).2

/-- Holomorphy of the actual Cauchy map across either exterior real ray. -/
theorem hasDerivAt_cauchy_exterior {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : ℂ} (hz : 1 < ‖z‖) :
    HasDerivAt (cauchy φ)
      ((Real.pi : ℂ)⁻¹ *
        ∫ s in Icc (-1 : ℝ) 1, (height φ s : ℂ) / (z - (s : ℂ)) ^ 2) z := by
  have hc : ContinuousOn (fun s : ℝ => (height φ s : ℂ)) (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp (height_continuous hφ)).continuousOn
  simpa only [cauchy, neg_div, integral_neg, neg_mul_neg] using!
    (hasDerivAt_cauchy_integral_exterior hc hz).const_mul (-((Real.pi : ℂ)⁻¹))

/-- The proved extension agrees with the original integral on the exterior
real axis; this is obtained from the genuine complex boundary limit. -/
theorem cauchyExtension_ofReal_exterior {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {x : ℝ} (hx : 1 < |x|) : cauchyExtension φ (x : ℂ) = cauchy φ (x : ℂ) := by
  have hc := hφ.continuous hα0
  have hlim := cauchy_boundary_vertical_tendsto_seq hφ hα0 hα1 hodd hzero x
  have hpath : Tendsto (fun n : ℕ =>
      (x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop (𝓝 (x : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add (h.mul_const Complex.I)
  have hlim' := (hasDerivAt_cauchy_exterior hc.continuousOn (by simpa using hx)).continuousAt.tendsto.comp hpath
  exact tendsto_nhds_unique hlim hlim'

/-- The boundary tangent on either exterior ray is the genuine positive
square-kernel integral, rather than an assumed Hilbert-transform formula. -/
theorem cauchyDerivativeExtension_ofReal_exterior {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {x : ℝ} (hx : 1 < |x|) :
    cauchyDerivativeExtension φ (x : ℂ) = (Real.pi : ℂ)⁻¹ *
      ∫ s in Icc (-1 : ℝ) 1, (height φ s : ℂ) / ((x : ℂ) - (s : ℂ)) ^ 2 := by
  have hd := (hasDerivAt_cauchy_exterior (hφ.continuous hα0).continuousOn
    (z := (x : ℂ)) (by simpa using hx)).comp_ofReal
  have heq : (fun t : ℝ => cauchyExtension φ (t : ℂ)) =ᶠ[𝓝 x]
      (fun t : ℝ => cauchy φ (t : ℂ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with t ht
    exact cauchyExtension_ofReal_exterior hφ hα0 hα1 hodd hzero ht
  exact (cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero x).unique
    (hd.congr_of_eventuallyEq heq)

end Torsion.Spectral

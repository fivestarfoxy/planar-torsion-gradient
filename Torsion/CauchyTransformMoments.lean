import Torsion.CauchyTransformDecay

/-!
# Infinity moments of the differentiated Cauchy transforms

These theorems justify the leading coefficients used when comparing the
holomorphic identity at infinity. No moment relation between M and N is
assumed or asserted here.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace Torsion.Spectral

private theorem norm_sub_real_lower (z : ℂ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    ‖z‖ - 1 ≤ ‖z - (s : ℂ)‖ := by
  have ha : |s| ≤ 1 := abs_le.2 hs
  have hn := norm_sub_norm_le z (s : ℂ)
  simp only [Complex.norm_real, Real.norm_eq_abs] at hn
  linarith

private theorem exterior_sub_real_ne_zero {z : ℂ} (hz : 1 < ‖z‖)
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) : z - (s : ℂ) ≠ 0 := by
  have hn := norm_sub_real_lower z hs
  exact norm_pos_iff.1 (by linarith : 0 < ‖z - (s : ℂ)‖)

private theorem exterior_kernel_continuousOn {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {z : ℂ} (hz : 1 < ‖z‖) :
    ContinuousOn (fun s : ℝ => f s / (z - (s : ℂ))) (Icc (-1 : ℝ) 1) :=
  hf.div (continuous_const.sub Complex.continuous_ofReal).continuousOn
    (fun _ hs => exterior_sub_real_ne_zero hz hs)

private theorem exterior_square_kernel_continuousOn {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {z : ℂ} (hz : 1 < ‖z‖) :
    ContinuousOn (fun s : ℝ => f s / (z - (s : ℂ)) ^ 2) (Icc (-1 : ℝ) 1) :=
  hf.div ((continuous_const.sub Complex.continuous_ofReal).pow 2).continuousOn
    (fun _ hs => pow_ne_zero 2 (exterior_sub_real_ne_zero hz hs))

theorem norm_cauchy_square_integral_le {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {z : ℂ} (hz : 1 < ‖z‖) :
    ‖∫ s in Icc (-1 : ℝ) 1, f s / (z - (s : ℂ)) ^ 2‖ ≤
      (∫ s in Icc (-1 : ℝ) 1, ‖f s‖) / (‖z‖ - 1) ^ 2 := by
  have hint : IntegrableOn (fun s : ℝ => f s / (z - (s : ℂ)) ^ 2)
      (Icc (-1 : ℝ) 1) := (exterior_square_kernel_continuousOn hf hz).integrableOn_Icc
  calc
    ‖∫ s in Icc (-1 : ℝ) 1, f s / (z - (s : ℂ)) ^ 2‖ ≤
        ∫ s in Icc (-1 : ℝ) 1, ‖f s / (z - (s : ℂ)) ^ 2‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Icc (-1 : ℝ) 1, ‖f s‖ / (‖z‖ - 1) ^ 2 := by
      apply setIntegral_mono_on hint.norm (hf.integrableOn_Icc.norm.div_const _) measurableSet_Icc
      intro s hs
      rw [norm_div, norm_pow]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos (sub_pos.2 hz))
        (pow_le_pow_left₀ (sub_pos.2 hz).le (norm_sub_real_lower z hs) 2)
    _ = (∫ s in Icc (-1 : ℝ) 1, ‖f s‖) / (‖z‖ - 1) ^ 2 := integral_div _ _

theorem cauchy_square_integral_tendsto_zero {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop) :
    Tendsto (fun a => ∫ s in Icc (-1 : ℝ) 1, f s / (z a - (s : ℂ)) ^ 2) l (𝓝 0) := by
  have hd : Tendsto (fun a => ‖z a‖ - 1) l atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [(Filter.tendsto_atTop.1 hz) (b + 1)] with a ha
    linarith
  have hsq : Tendsto (fun a => (‖z a‖ - 1) ^ 2) l atTop := by
    simpa only [pow_two] using hd.atTop_mul_atTop₀ hd
  apply squeeze_zero_norm' _ (hsq.const_div_atTop (∫ s in Icc (-1 : ℝ) 1, ‖f s‖))
  filter_upwards [hz.eventually (eventually_gt_atTop 1)] with a ha
  exact norm_cauchy_square_integral_le hf ha

private theorem cauchy_square_integral_moment_error {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {z : ℂ} (hz : 1 < ‖z‖) :
    z ^ 2 * (∫ s in Icc (-1 : ℝ) 1, f s / (z - (s : ℂ)) ^ 2) -
        (∫ s in Icc (-1 : ℝ) 1, f s) =
      2 * (∫ s in Icc (-1 : ℝ) 1, (f s * (s : ℂ)) / (z - (s : ℂ))) +
        ∫ s in Icc (-1 : ℝ) 1, (f s * (s : ℂ) ^ 2) / (z - (s : ℂ)) ^ 2 := by
  have hint : IntegrableOn (fun s : ℝ => f s / (z - (s : ℂ)) ^ 2)
      (Icc (-1 : ℝ) 1) := (exterior_square_kernel_continuousOn hf hz).integrableOn_Icc
  have hf₁ : ContinuousOn (fun s : ℝ => f s * (s : ℂ)) (Icc (-1 : ℝ) 1) :=
    hf.mul Complex.continuous_ofReal.continuousOn
  have hf₂ : ContinuousOn (fun s : ℝ => f s * (s : ℂ) ^ 2) (Icc (-1 : ℝ) 1) :=
    hf.mul (Complex.continuous_ofReal.pow 2).continuousOn
  have hi₁ : IntegrableOn (fun s : ℝ => (f s * (s : ℂ)) / (z - (s : ℂ)))
      (Icc (-1 : ℝ) 1) := (exterior_kernel_continuousOn hf₁ hz).integrableOn_Icc
  have hi₂ : IntegrableOn (fun s : ℝ => (f s * (s : ℂ) ^ 2) / (z - (s : ℂ)) ^ 2)
      (Icc (-1 : ℝ) 1) := (exterior_square_kernel_continuousOn hf₂ hz).integrableOn_Icc
  rw [← integral_const_mul, ← integral_sub (hint.const_mul (z ^ 2)) hf.integrableOn_Icc,
    ← integral_const_mul, ← integral_add (hi₁.const_mul 2) hi₂]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  field_simp [exterior_sub_real_ne_zero hz hs]
  ring

/-- The differentiated kernel has leading coefficient equal to the same
zeroth density moment. This is the limit used for `F'` and `A'`. -/
theorem cauchy_square_integral_moment {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop) :
    Tendsto (fun a => z a ^ 2 * ∫ s in Icc (-1 : ℝ) 1, f s / (z a - (s : ℂ)) ^ 2) l
      (𝓝 (∫ s in Icc (-1 : ℝ) 1, f s)) := by
  have hf₁ : ContinuousOn (fun s : ℝ => f s * (s : ℂ)) (Icc (-1 : ℝ) 1) :=
    hf.mul Complex.continuous_ofReal.continuousOn
  have hf₂ : ContinuousOn (fun s : ℝ => f s * (s : ℂ) ^ 2) (Icc (-1 : ℝ) 1) :=
    hf.mul (Complex.continuous_ofReal.pow 2).continuousOn
  have herr : Tendsto (fun a => z a ^ 2 *
      (∫ s in Icc (-1 : ℝ) 1, f s / (z a - (s : ℂ)) ^ 2) -
      (∫ s in Icc (-1 : ℝ) 1, f s)) l (𝓝 0) := by
    have h := ((cauchy_integral_tendsto_zero hf₁ hz).const_mul 2).add
      (cauchy_square_integral_tendsto_zero hf₂ hz)
    simp only [mul_zero, zero_add] at h
    apply h.congr'
    filter_upwards [hz.eventually (eventually_gt_atTop 1)] with a ha
    exact (cauchy_square_integral_moment_error hf ha).symm
  simpa only [sub_add_cancel, zero_add] using herr.add_const (∫ s in Icc (-1 : ℝ) 1, f s)

/-- The actual derivative `F'` tends to zero at infinity within H. -/
theorem cauchy_derivative_tendsto_zero {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop)
    (hH : ∀ᶠ a in l, z a ∈ upperHalfPlane) :
    Tendsto (fun a => deriv (cauchy φ) (z a)) l (𝓝 0) := by
  have hc : ContinuousOn (fun s : ℝ => (height φ s : ℂ)) (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp (height_continuous hφ)).continuousOn
  have h := (cauchy_square_integral_tendsto_zero hc hz).const_mul ((Real.pi : ℂ)⁻¹)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [hH] with a ha
  exact (deriv_cauchy_eq hφ ha).symm

/-- The leading coefficient of `F'` is the concrete moment `M/π`. -/
theorem cauchy_derivative_moment {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop)
    (hH : ∀ᶠ a in l, z a ∈ upperHalfPlane) :
    Tendsto (fun a => z a ^ 2 * deriv (cauchy φ) (z a)) l
      (𝓝 ((Real.pi : ℂ)⁻¹ * (mass φ : ℂ))) := by
  have hc : ContinuousOn (fun s : ℝ => (height φ s : ℂ)) (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp (height_continuous hφ)).continuousOn
  have h := (cauchy_square_integral_moment hc hz).const_mul ((Real.pi : ℂ)⁻¹)
  simp only [integral_complex_ofReal] at h
  unfold mass
  apply h.congr'
  filter_upwards [hH] with a ha
  rw [deriv_cauchy_eq hφ ha]
  ring

/-- The actual derivative `A'` tends to zero at infinity within H. -/
theorem auxiliary_derivative_tendsto_zero {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop)
    (hH : ∀ᶠ a in l, z a ∈ upperHalfPlane) :
    Tendsto (fun a => deriv (auxiliary φ) (z a)) l (𝓝 0) := by
  have hc : ContinuousOn (fun s : ℝ => (((height φ s) ^ 2 : ℝ) : ℂ))
      (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp ((height_continuous hφ).pow 2)).continuousOn
  have h := (cauchy_square_integral_tendsto_zero hc hz).const_mul ((2 * Real.pi : ℂ)⁻¹)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [hH] with a ha
  exact (deriv_auxiliary_eq hφ ha).symm

/-- The leading coefficient of `A'` is the concrete moment `N/(2π)`. -/
theorem auxiliary_derivative_moment {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop)
    (hH : ∀ᶠ a in l, z a ∈ upperHalfPlane) :
    Tendsto (fun a => z a ^ 2 * deriv (auxiliary φ) (z a)) l
      (𝓝 ((2 * Real.pi : ℂ)⁻¹ * (squareMass φ : ℂ))) := by
  have hc : ContinuousOn (fun s : ℝ => (((height φ s) ^ 2 : ℝ) : ℂ))
      (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp ((height_continuous hφ).pow 2)).continuousOn
  have h := (cauchy_square_integral_moment hc hz).const_mul ((2 * Real.pi : ℂ)⁻¹)
  simp only [integral_complex_ofReal] at h
  unfold squareMass
  apply h.congr'
  filter_upwards [hH] with a ha
  rw [deriv_auxiliary_eq hφ ha]
  ring

end Torsion.Spectral

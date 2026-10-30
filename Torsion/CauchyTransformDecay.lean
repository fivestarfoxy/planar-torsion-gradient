module

public import Torsion.CauchyTransform
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Decay of the concrete Cauchy transform

The estimates are for the defining integrals, uniformly in the direction
in which the complex parameter escapes to infinity.
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

/-- The Cauchy integral is controlled by its density's L¹ norm and the
distance `‖z‖-1` to the integration interval. -/
theorem norm_cauchy_integral_le {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {z : ℂ} (hz : 1 < ‖z‖) :
    ‖∫ s in Icc (-1 : ℝ) 1, f s / (z - (s : ℂ))‖ ≤
      (∫ s in Icc (-1 : ℝ) 1, ‖f s‖) / (‖z‖ - 1) := by
  have hint : IntegrableOn (fun s : ℝ => f s / (z - (s : ℂ))) (Icc (-1 : ℝ) 1) :=
    (exterior_kernel_continuousOn hf hz).integrableOn_Icc
  calc
    ‖∫ s in Icc (-1 : ℝ) 1, f s / (z - (s : ℂ))‖ ≤
        ∫ s in Icc (-1 : ℝ) 1, ‖f s / (z - (s : ℂ))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Icc (-1 : ℝ) 1, ‖f s‖ / (‖z‖ - 1) := by
      apply setIntegral_mono_on hint.norm (hf.integrableOn_Icc.norm.div_const _) measurableSet_Icc
      intro s hs
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.2 hz) (norm_sub_real_lower z hs)
    _ = (∫ s in Icc (-1 : ℝ) 1, ‖f s‖) / (‖z‖ - 1) := integral_div _ _

/-- The compact Cauchy integral vanishes along every parameter whose norm
tends to infinity. -/
theorem cauchy_integral_tendsto_zero {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop) :
    Tendsto (fun a => ∫ s in Icc (-1 : ℝ) 1, f s / (z a - (s : ℂ))) l (𝓝 0) := by
  have hd : Tendsto (fun a => ‖z a‖ - 1) l atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [(Filter.tendsto_atTop.1 hz) (b + 1)] with a ha
    linarith
  apply squeeze_zero_norm' _ (hd.const_div_atTop (∫ s in Icc (-1 : ℝ) 1, ‖f s‖))
  filter_upwards [hz.eventually (eventually_gt_atTop 1)] with a ha
  exact norm_cauchy_integral_le hf ha

private theorem cauchy_integral_first_moment_error {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {z : ℂ} (hz : 1 < ‖z‖) :
    z * (∫ s in Icc (-1 : ℝ) 1, f s / (z - (s : ℂ))) -
        (∫ s in Icc (-1 : ℝ) 1, f s) =
      ∫ s in Icc (-1 : ℝ) 1, (f s * (s : ℂ)) / (z - (s : ℂ)) := by
  have hint : IntegrableOn (fun s : ℝ => f s / (z - (s : ℂ))) (Icc (-1 : ℝ) 1) :=
    (exterior_kernel_continuousOn hf hz).integrableOn_Icc
  rw [← integral_const_mul, ← integral_sub (hint.const_mul z) hf.integrableOn_Icc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  field_simp [exterior_sub_real_ne_zero hz hs]
  ring

/-- The leading moment at infinity: multiplication by the complex parameter
recovers the density's integral. This is an actual asymptotic theorem for
the Cauchy integral, rather than a formal Laurent-series calculation. -/
theorem cauchy_integral_first_moment {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop) :
    Tendsto (fun a => z a * ∫ s in Icc (-1 : ℝ) 1, f s / (z a - (s : ℂ))) l
      (𝓝 (∫ s in Icc (-1 : ℝ) 1, f s)) := by
  have hf' : ContinuousOn (fun s : ℝ => f s * (s : ℂ)) (Icc (-1 : ℝ) 1) :=
    hf.mul Complex.continuous_ofReal.continuousOn
  have herr : Tendsto (fun a => z a * (∫ s in Icc (-1 : ℝ) 1, f s / (z a - (s : ℂ))) -
      (∫ s in Icc (-1 : ℝ) 1, f s)) l (𝓝 0) := by
    apply (cauchy_integral_tendsto_zero hf' hz).congr'
    filter_upwards [hz.eventually (eventually_gt_atTop 1)] with a ha
    exact (cauchy_integral_first_moment_error hf ha).symm
  simpa only [sub_add_cancel, zero_add] using herr.add_const (∫ s in Icc (-1 : ℝ) 1, f s)

/-- Decay of the transform in (1.4), for arbitrary escape directions. -/
theorem cauchy_tendsto_zero {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop) :
    Tendsto (fun a => cauchy φ (z a)) l (𝓝 0) := by
  have hc : ContinuousOn (fun s : ℝ => (height φ s : ℂ)) (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp (height_continuous hφ)).continuousOn
  simpa only [cauchy, mul_zero] using (cauchy_integral_tendsto_zero hc hz).const_mul
    (-((Real.pi : ℂ)⁻¹))

/-- Decay of the auxiliary transform in (5.3). -/
theorem auxiliary_tendsto_zero {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop) :
    Tendsto (fun a => auxiliary φ (z a)) l (𝓝 0) := by
  have hc : ContinuousOn (fun s : ℝ => (((height φ s) ^ 2 : ℝ) : ℂ))
      (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp ((height_continuous hφ).pow 2)).continuousOn
  simpa only [auxiliary, mul_zero] using (cauchy_integral_tendsto_zero hc hz).const_mul
    (-((2 * Real.pi : ℂ)⁻¹))

/-- The coefficient of `1/z` in the concrete transform is `-M/π`. -/
theorem cauchy_first_moment {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop) :
    Tendsto (fun a => z a * cauchy φ (z a)) l
      (𝓝 (-((Real.pi : ℂ)⁻¹) * (mass φ : ℂ))) := by
  have hc : ContinuousOn (fun s : ℝ => (height φ s : ℂ)) (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp (height_continuous hφ)).continuousOn
  have h := (cauchy_integral_first_moment hc hz).const_mul (-((Real.pi : ℂ)⁻¹))
  simp only [integral_complex_ofReal] at h
  unfold mass
  convert h using 1
  funext a
  dsimp [cauchy]
  ring

/-- The coefficient of `1/z` in the auxiliary transform is `-N/(2π)`. -/
theorem auxiliary_first_moment {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop) :
    Tendsto (fun a => z a * auxiliary φ (z a)) l
      (𝓝 (-((2 * Real.pi : ℂ)⁻¹) * (squareMass φ : ℂ))) := by
  have hc : ContinuousOn (fun s : ℝ => (((height φ s) ^ 2 : ℝ) : ℂ))
      (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp ((height_continuous hφ).pow 2)).continuousOn
  have h := (cauchy_integral_first_moment hc hz).const_mul (-((2 * Real.pi : ℂ)⁻¹))
  simp only [integral_complex_ofReal] at h
  unfold squareMass
  convert h using 1
  funext a
  dsimp [auxiliary]
  ring

end Torsion.Spectral

module

public import Torsion.CauchyTransform
public import Torsion.CauchyTransformHeightDerivative
public import Torsion.CauchyTransformIntegrationByParts
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The imaginary boundary trace of the Cauchy transform

The Poisson kernel is an approximate identity. Applying the proved
approximate-identity theorem gives the actual vertical boundary trace of the
imaginary part of F. This is one component of the Plemelj boundary theorem;
the real principal-value trace and its Hölder regularity are separate steps.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace Torsion.Spectral

def poissonDensity (t : ℝ) : ℝ := Real.pi⁻¹ * (1 + t ^ 2)⁻¹

theorem poissonDensity_nonneg (t : ℝ) : 0 ≤ poissonDensity t := by
  unfold poissonDensity
  positivity

theorem integral_poissonDensity : (∫ t : ℝ, poissonDensity t) = 1 := by
  simp only [poissonDensity]
  rw [integral_const_mul, integral_univ_inv_one_add_sq]
  exact inv_mul_cancel₀ Real.pi_ne_zero

theorem poissonDensity_tail :
    Tendsto (fun t : ℝ => ‖t‖ * poissonDensity t) (Bornology.cobounded ℝ) (𝓝 0) := by
  have hn : Tendsto (fun t : ℝ => ‖t‖) (Bornology.cobounded ℝ) atTop :=
    tendsto_norm_cobounded_atTop
  apply squeeze_zero' (Eventually.of_forall fun t => mul_nonneg (norm_nonneg t)
    (poissonDensity_nonneg t)) _ (hn.const_div_atTop Real.pi⁻¹)
  filter_upwards [hn.eventually (eventually_gt_atTop 0)] with t ht
  have hsq : 0 < 1 + t ^ 2 := by positivity
  have ht' : 0 < |t| := by simpa only [Real.norm_eq_abs] using ht
  have hi : |t| / (1 + t ^ 2) ≤ 1 / |t| := by
    apply (div_le_iff₀ hsq).2
    have hi' : |t| ≤ (1 + t ^ 2) / |t| := (le_div_iff₀ ht').2 (by nlinarith [sq_abs t])
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using hi'
  have hm := mul_le_mul_of_nonneg_left hi (inv_nonneg.2 Real.pi_pos.le)
  simpa only [poissonDensity, Real.norm_eq_abs, div_eq_mul_inv, mul_one,
    mul_comm, mul_left_comm, mul_assoc] using hm

/-- The one-dimensional Poisson densities form a concrete approximate
identity for every integrable function continuous at the marked point. -/
theorem poisson_peak_limit {g : ℝ → ℝ} {x : ℝ}
    (hg : Integrable g) (hx : ContinuousAt g x) :
    Tendsto (fun c : ℝ => ∫ s : ℝ,
      (c * poissonDensity (c * (x - s))) * g s) atTop (𝓝 (g x)) := by
  simpa only [Module.finrank_self, pow_one, smul_eq_mul] using
    tendsto_integral_comp_smul_smul_of_integrable'
      poissonDensity_nonneg integral_poissonDensity
      (by simpa only [Module.finrank_self, pow_one] using poissonDensity_tail) hg hx

private theorem denominator_ne_zero {z : ℂ} (hz : z ∈ upperHalfPlane) (s : ℝ) :
    z - (s : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
  exact hz.ne' hi

/-- The imaginary part of the defining complex integral is precisely its
Poisson integral, with the sign and factor `1/π` of the writeup. -/
theorem cauchy_im_eq_poisson {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (cauchy φ z).im = ∫ s in Icc (-1 : ℝ) 1,
      (Real.pi⁻¹ * z.im / ((z.re - s) ^ 2 + z.im ^ 2)) * height φ s := by
  have hYc : Continuous (fun s : ℝ => (height φ s : ℂ)) :=
    Complex.continuous_ofReal.comp (height_continuous hφ)
  have hint : IntegrableOn (fun s : ℝ => (height φ s : ℂ) / (z - (s : ℂ)))
      (Icc (-1 : ℝ) 1) :=
    (hYc.div (continuous_const.sub Complex.continuous_ofReal)
      (denominator_ne_zero hz)).integrableOn_Icc
  unfold cauchy
  rw [← integral_const_mul]
  have him : (∫ s in Icc (-1 : ℝ) 1,
      -((Real.pi : ℂ)⁻¹) * ((height φ s : ℂ) / (z - (s : ℂ)))).im =
      ∫ s in Icc (-1 : ℝ) 1,
      (-((Real.pi : ℂ)⁻¹) * ((height φ s : ℂ) / (z - (s : ℂ)))).im :=
    (integral_im (hint.const_mul (-((Real.pi : ℂ)⁻¹)))).symm
  rw [him]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s _
  rw [← Complex.ofReal_inv, ← Complex.ofReal_neg]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_im,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply, zero_mul, zero_div,
    sub_zero, zero_sub]
  ring

/-- Positivity of the spectral profile puts the image of F in the upper
half-plane, before any univalence or convexity assertion. -/
theorem cauchy_im_pos {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    0 < (cauchy φ z).im := by
  rw [cauchy_im_eq_poisson hφ hz, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  have hz' : 0 < z.im := hz
  have hden : Continuous (fun s : ℝ => (z.re - s) ^ 2 + z.im ^ 2) := by fun_prop
  have hk : Continuous (fun s : ℝ =>
      (Real.pi⁻¹ * z.im / ((z.re - s) ^ 2 + z.im ^ 2)) * height φ s) :=
    (continuous_const.div hden (fun s => ne_of_gt (by positivity))).mul (height_continuous hφ)
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (hk.intervalIntegrable (-1) 1)
    (fun s hs => mul_pos (div_pos (mul_pos (inv_pos.2 Real.pi_pos) hz') (by positivity))
      (height_pos hφ hpos (abs_lt.2 hs))) (by norm_num)

theorem cauchy_mapsTo_upperHalfPlane {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    MapsTo (cauchy φ) upperHalfPlane upperHalfPlane :=
  fun _ hz => cauchy_im_pos hφ hpos hz

/-- An exact identity between a vertical Cauchy value and the rescaled
one-dimensional Poisson density. -/
theorem cauchy_im_eq_poisson_peak {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) (x : ℝ) {c : ℝ} (hc : 0 < c) :
    (cauchy φ ((x : ℂ) + (c⁻¹ : ℝ) * Complex.I)).im =
      ∫ s : ℝ, (c * poissonDensity (c * (x - s))) * height φ s := by
  have hz : (x : ℂ) + (c⁻¹ : ℝ) * Complex.I ∈ upperHalfPlane := by
    simpa [upperHalfPlane] using inv_pos.2 hc
  rw [cauchy_im_eq_poisson hφ hz]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, zero_mul, zero_add]
  have hglobal :
      (∫ s in Icc (-1 : ℝ) 1, (c * poissonDensity (c * (x - s))) * height φ s) =
        ∫ s : ℝ, (c * poissonDensity (c * (x - s))) * height φ s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    have hnot : ¬ |s| < 1 := fun h => hs (abs_le.1 h.le)
    simp [height, hnot]
  rw [← hglobal]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s _
  unfold poissonDensity
  have hd : (x - s) ^ 2 + (c⁻¹) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hd' : 1 + (c * (x - s)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hc.ne', hd, hd']
  ring

/-- The actual vertical imaginary boundary trace is the integrated profile.
The parameterization is `z = x + i/c`, with `c → +∞`. -/
theorem cauchy_im_vertical_boundary {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) (x : ℝ) :
    Tendsto (fun c : ℝ => (cauchy φ ((x : ℂ) + (c⁻¹ : ℝ) * Complex.I)).im)
      atTop (𝓝 (height φ x)) := by
  apply (poisson_peak_limit (height_integrable hφ) (height_continuous hφ).continuousAt).congr'
  filter_upwards [eventually_gt_atTop 0] with c hc
  exact (cauchy_im_eq_poisson_peak hφ x hc).symm

/-- The same normalized Cauchy integral for an arbitrary real density. -/
def realCauchy (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  -((Real.pi : ℂ)⁻¹) * ∫ s in Icc (-1 : ℝ) 1, (f s : ℂ) / (z - (s : ℂ))

theorem realCauchy_im_eq_poisson {f : ℝ → ℝ}
    (hf : Continuous f) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (realCauchy f z).im = ∫ s in Icc (-1 : ℝ) 1,
      (Real.pi⁻¹ * z.im / ((z.re - s) ^ 2 + z.im ^ 2)) * f s := by
  have hfc : Continuous (fun s : ℝ => (f s : ℂ)) := Complex.continuous_ofReal.comp hf
  have hint : IntegrableOn (fun s : ℝ => (f s : ℂ) / (z - (s : ℂ)))
      (Icc (-1 : ℝ) 1) :=
    (hfc.div (continuous_const.sub Complex.continuous_ofReal)
      (denominator_ne_zero hz)).integrableOn_Icc
  unfold realCauchy
  rw [← integral_const_mul]
  have him : (∫ s in Icc (-1 : ℝ) 1,
      -((Real.pi : ℂ)⁻¹) * ((f s : ℂ) / (z - (s : ℂ)))).im =
      ∫ s in Icc (-1 : ℝ) 1,
      (-((Real.pi : ℂ)⁻¹) * ((f s : ℂ) / (z - (s : ℂ)))).im :=
    (integral_im (hint.const_mul (-((Real.pi : ℂ)⁻¹)))).symm
  rw [him]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s _
  rw [← Complex.ofReal_inv, ← Complex.ofReal_neg]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_im,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply, zero_mul, zero_div,
    sub_zero, zero_sub]
  ring

theorem realCauchy_im_eq_poisson_peak {f : ℝ → ℝ}
    (hf : Continuous f) (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0)
    (x : ℝ) {c : ℝ} (hc : 0 < c) :
    (realCauchy f ((x : ℂ) + (c⁻¹ : ℝ) * Complex.I)).im =
      ∫ s : ℝ, (c * poissonDensity (c * (x - s))) * f s := by
  have hz : (x : ℂ) + (c⁻¹ : ℝ) * Complex.I ∈ upperHalfPlane := by
    simpa [upperHalfPlane] using inv_pos.2 hc
  rw [realCauchy_im_eq_poisson hf hz]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, zero_mul, zero_add]
  have hglobal :
      (∫ s in Icc (-1 : ℝ) 1, (c * poissonDensity (c * (x - s))) * f s) =
        ∫ s : ℝ, (c * poissonDensity (c * (x - s))) * f s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    have hnot : ¬ |s| < 1 := fun h => hs (abs_le.1 h.le)
    rw [hzero s (le_of_not_gt hnot), mul_zero]
  rw [← hglobal]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s _
  unfold poissonDensity
  have hd : (x - s) ^ 2 + (c⁻¹) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hd' : 1 + (c * (x - s)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hc.ne', hd, hd']
  ring

/-- Vertical imaginary trace for every continuous density supported in the
integration interval. This also applies to the spectral data φ and Y². -/
theorem realCauchy_im_vertical_boundary {f : ℝ → ℝ}
    (hf : Continuous f) (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) (x : ℝ) :
    Tendsto (fun c : ℝ => (realCauchy f ((x : ℂ) + (c⁻¹ : ℝ) * Complex.I)).im)
      atTop (𝓝 (f x)) := by
  have hsupp : HasCompactSupport f := by
    apply HasCompactSupport.intro (K := Icc (-1 : ℝ) 1) isCompact_Icc
    intro s hs
    have hnot : ¬ |s| < 1 := fun h => hs (abs_le.1 h.le)
    exact hzero s (le_of_not_gt hnot)
  apply (poisson_peak_limit (hf.integrable_of_hasCompactSupport hsupp) hf.continuousAt).congr'
  filter_upwards [eventually_gt_atTop 0] with c hc
  exact (realCauchy_im_eq_poisson_peak hf hzero x hc).symm

/-- The auxiliary transform has the actual imaginary boundary trace Y²/2. -/
theorem auxiliary_im_vertical_boundary {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) (x : ℝ) :
    Tendsto (fun c : ℝ => (auxiliary φ ((x : ℂ) + (c⁻¹ : ℝ) * Complex.I)).im)
      atTop (𝓝 ((height φ x) ^ 2 / 2)) := by
  have h := (realCauchy_im_vertical_boundary (f := fun s => (height φ s) ^ 2)
    (by simpa only [Pi.pow_apply] using! (height_continuous hφ).pow 2)
    (fun s hs => by rw [height_zero_of_one_le_abs φ hs]; norm_num) x).const_mul (1 / 2 : ℝ)
  have heq (z : ℂ) : auxiliary φ z = (1 / 2 : ℂ) *
      realCauchy (fun s => (height φ s) ^ 2) z := by
    unfold auxiliary realCauchy
    simp only [mul_inv_rev]
    ring
  convert h using 1
  · funext c
    rw [heq]
    simp only [Complex.mul_im]
    norm_num
  · congr 1
    ring

/-- The actual vertical imaginary trace of F' equals -φ, as required by
Lemma 2.2 applied to the derivative density. -/
theorem cauchy_derivative_im_vertical_boundary {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) (x : ℝ) :
    Tendsto (fun c : ℝ => (deriv (cauchy φ)
      ((x : ℂ) + (c⁻¹ : ℝ) * Complex.I)).im) atTop (𝓝 (-φ x)) := by
  apply (realCauchy_im_vertical_boundary hφ hzero x).neg.congr'
  filter_upwards [eventually_gt_atTop 0] with c hc
  have hz : (x : ℂ) + (c⁻¹ : ℝ) * Complex.I ∈ upperHalfPlane := by
    simpa [upperHalfPlane] using inv_pos.2 hc
  rw [deriv_cauchy_eq_eigenfunction_integral hφ hodd hzero hz]
  simp only [realCauchy, neg_mul, Complex.neg_im, neg_neg]

/-- The auxiliary derivative has the actual vertical imaginary trace
`-Yφ = YY'`, providing the imaginary boundary identity in Lemma 5.2. -/
theorem auxiliary_derivative_im_vertical_boundary {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) (x : ℝ) :
    Tendsto (fun c : ℝ => (deriv (auxiliary φ)
      ((x : ℂ) + (c⁻¹ : ℝ) * Complex.I)).im)
      atTop (𝓝 (-(height φ x * φ x))) := by
  have hY := height_continuous hφ.continuousOn
  apply (realCauchy_im_vertical_boundary (f := fun s => height φ s * φ s)
    (by fun_prop)
    (fun s hs => by rw [height_zero_of_one_le_abs φ hs, zero_mul]) x).neg.congr'
  filter_upwards [eventually_gt_atTop 0] with c hc
  have hz : (x : ℂ) + (c⁻¹ : ℝ) * Complex.I ∈ upperHalfPlane := by
    simpa [upperHalfPlane] using inv_pos.2 hc
  rw [deriv_auxiliary_eq_product_integral hφ hodd hzero hz]
  simp only [realCauchy, neg_mul, Complex.neg_im, neg_neg]

end Torsion.Spectral

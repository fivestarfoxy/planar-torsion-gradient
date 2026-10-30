module

public import Torsion.RestrictedSpectralBoundaryPrimitive
public import Torsion.RestrictedSpectralRegularRepresentative
public import Torsion.FourierHilbertPairing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The actual energy kernel for separated integrable data

Schwartz decay of the genuine test transform makes the original Fourier
energy pairing integrable even when the first datum is only L¹. This also
justifies removal of exponential damping without a finite-energy premise
on that first datum. Uniform support separation gives two ordinary dominated
limits and a C¹ resolvent. Classical compact-test integration by parts then
identifies the original energy with the actual double-pole kernel.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- Actual first weighted L¹ moment of the Fourier transform of a genuine
compact smooth test. -/
theorem IsCore.integrable_abs_mul_norm_fourier {ψ : ℝ → ℝ} (hψ : IsCore ψ) :
    Integrable (fun ξ : ℝ => |ξ| * ‖fourier ψ ξ‖) := by
  let ψS := compactSmoothSchwartz hψ.1 hψ.2.1
  let S := SchwartzMap.fourierTransformCLM ℂ ψS
  have hF (ξ : ℝ) : fourier ψ ξ = S (ξ / (2 * Real.pi)) := fourier_eq_mathlib ψ ξ
  have hp : 0 < 2 * Real.pi := by positivity
  have hi : Integrable (fun ξ : ℝ => ‖ξ‖ * ‖S ξ‖) := by
    simpa only [pow_one] using S.integrable_pow_mul volume 1
  have hid := hi.comp_div hp.ne'
  convert hid.const_mul (2 * Real.pi) using 1
  funext ξ
  rw [hF, Real.norm_eq_abs, abs_div, abs_of_pos hp]
  field_simp

/-- The original Fourier form against a smooth compact test is absolutely
integrable for every actual L¹ datum. -/
theorem energy_integrand_integrable_of_integrable_core {r ψ : ℝ → ℝ}
    (hr : Integrable r) (hψ : IsCore ψ) :
    Integrable (fun ξ : ℝ => |ξ| * (fourier r ξ * star (fourier ψ ξ)).re) := by
  have hψi := hψ.memRestrictedFormDomain.integrable
  apply (hψ.integrable_abs_mul_norm_fourier.const_mul (∫ s : ℝ, ‖r s‖)).mono'
  · exact (continuous_abs.mul (Complex.continuous_re.comp ((fourier_continuous hr).mul
      (fourier_continuous hψi).star))).aestronglyMeasurable
  · exact ae_of_all _ fun ξ => by
      rw [norm_mul, Real.norm_eq_abs, abs_abs, Real.norm_eq_abs]
      calc
        |ξ| * |(fourier r ξ * star (fourier ψ ξ)).re| ≤
            |ξ| * ‖fourier r ξ * star (fourier ψ ξ)‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
        _ = |ξ| * (‖fourier r ξ‖ * ‖fourier ψ ξ‖) := by rw [norm_mul, norm_star]
        _ ≤ |ξ| * ((∫ s : ℝ, ‖r s‖) * ‖fourier ψ ξ‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (norm_fourier_le_integral_norm r ξ) (norm_nonneg _)) (abs_nonneg _)
        _ = _ := by ring

/-- Removing the actual exponential damping only needs L¹ for the first
datum when the second datum is a genuine core test. -/
theorem damped_energy_tendsto_of_integrable_core {r ψ : ℝ → ℝ}
    (hr : Integrable r) (hψ : IsCore ψ) :
    Tendsto (fun y : ℝ => (1 / (2 * Real.pi)) * ∫ ξ : ℝ,
      Real.exp (-y * |ξ|) * |ξ| * (fourier r ξ * star (fourier ψ ξ)).re)
      (𝓝[>] 0) (𝓝 (energy r ψ)) := by
  let G : ℝ → ℝ := fun ξ => |ξ| * (fourier r ξ * star (fourier ψ ξ)).re
  have hG : Integrable G := energy_integrand_integrable_of_integrable_core hr hψ
  have hmeas (y : ℝ) : AEStronglyMeasurable (fun ξ : ℝ => Real.exp (-y * |ξ|) * G ξ) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable.mul
      hG.aestronglyMeasurable
  have hbound : ∀ᶠ y : ℝ in 𝓝[>] 0,
      ∀ᵐ ξ : ℝ, ‖Real.exp (-y * |ξ|) * G ξ‖ ≤ ‖G ξ‖ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ae_of_all _ fun ξ => by
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
      apply mul_le_of_le_one_left (norm_nonneg _)
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hy.le) (abs_nonneg _))
  have hpoint : ∀ᵐ ξ : ℝ, Tendsto (fun y : ℝ => Real.exp (-y * |ξ|) * G ξ)
      (𝓝[>] 0) (𝓝 (G ξ)) := by
    exact ae_of_all _ fun ξ => by
      have hc : ContinuousAt (fun y : ℝ => Real.exp (-y * |ξ|) * G ξ) 0 := by fun_prop
      simpa using hc.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hi := tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖G ξ‖)
    (Eventually.of_forall hmeas) hbound hG.norm hpoint
  simpa only [G, energy, mul_assoc] using hi.const_mul (1 / (2 * Real.pi))

private theorem exterior_gap_le_abs_sub {x u s : ℝ}
    (_hx : |x| < 1) (hu : u ∈ ball x ((1 - |x|) / 2))
    (hs : s ∉ Ioo (-1 : ℝ) 1) : (1 - |x|) / 2 ≤ |u - s| := by
  have hus : |u - x| < (1 - |x|) / 2 := by
    simpa only [mem_ball, Real.dist_eq] using hu
  have hsabs : 1 ≤ |s| := le_of_not_gt (fun h => hs (abs_lt.1 h))
  have huabs := abs_sub_abs_le_abs_sub u x
  have hsu := abs_sub_abs_le_abs_sub s u
  rw [abs_sub_comm s u] at hsu
  linarith

/-- Uniform separation from the exterior support gives the actual L¹
resolvent powers at every interior point. -/
theorem integrable_exterior_div_pow {r : ℝ → ℝ} (hr : Integrable r)
    (hzero : ∀ᵐ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → r s = 0)
    {x : ℝ} (hx : |x| < 1) (m : ℕ) :
    Integrable (fun s : ℝ => r s / (x - s) ^ m) := by
  have hε : 0 < (1 - |x|) / 2 := by linarith
  have hm : AEStronglyMeasurable (fun s : ℝ => r s / (x - s) ^ m) := by
    simpa only [div_eq_mul_inv] using hr.aestronglyMeasurable.mul
      (((continuous_const.sub continuous_id).pow m).measurable.inv.aestronglyMeasurable)
  apply (hr.norm.div_const (((1 - |x|) / 2) ^ m)).mono' hm
  filter_upwards [hzero] with s hs
  by_cases hsi : s ∈ Ioo (-1 : ℝ) 1
  · simp [hs hsi]
  · rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hε m)
    exact pow_le_pow_left₀ hε.le
      (exterior_gap_le_abs_sub hx (mem_ball_self hε) hsi) m

/-- Continuity of each actual exterior-data resolvent power inside the
source-free interval, proved by ordinary dominated convergence. -/
theorem continuousAt_integral_exterior_div_pow {r : ℝ → ℝ} (hr : Integrable r)
    (hzero : ∀ᵐ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → r s = 0)
    {x : ℝ} (hx : |x| < 1) (m : ℕ) :
    ContinuousAt (fun u : ℝ => ∫ s : ℝ, r s / (u - s) ^ m) x := by
  have hε : 0 < (1 - |x|) / 2 := by linarith
  apply continuousAt_of_dominated
    (bound := fun s : ℝ => ‖r s‖ / (((1 - |x|) / 2) ^ m))
  · exact Eventually.of_forall fun u => by
      simpa only [div_eq_mul_inv] using hr.aestronglyMeasurable.mul
        (((continuous_const.sub continuous_id).pow m).measurable.inv.aestronglyMeasurable)
  · filter_upwards [ball_mem_nhds x hε] with u hu
    filter_upwards [hzero] with s hs
    by_cases hsi : s ∈ Ioo (-1 : ℝ) 1
    · simp [hs hsi]
    · rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      apply div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hε m)
      exact pow_le_pow_left₀ hε.le (exterior_gap_le_abs_sub hx hu hsi) m
  · exact hr.norm.div_const _
  · filter_upwards [hzero] with s hs
    by_cases hsi : s ∈ Ioo (-1 : ℝ) 1
    · simp only [hs hsi, zero_div]
      exact continuousAt_const
    · have hne : x - s ≠ 0 :=
        abs_pos.1 (hε.trans_le (exterior_gap_le_abs_sub hx (mem_ball_self hε) hsi))
      exact continuousAt_const.div ((continuousAt_id.sub continuousAt_const).pow m)
        (pow_ne_zero m hne)

/-- Ordinary differentiation of the genuine exterior Cauchy resolvent
on the source-free open interval. -/
theorem hasDerivAt_integral_exterior_div {r : ℝ → ℝ} (hr : Integrable r)
    (hzero : ∀ᵐ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → r s = 0)
    {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun u : ℝ => ∫ s : ℝ, r s / (u - s))
      (-(∫ s : ℝ, r s / (x - s) ^ 2)) x := by
  have hε : 0 < (1 - |x|) / 2 := by linarith
  have hmeas (u : ℝ) : AEStronglyMeasurable (fun s : ℝ => r s / (u - s)) := by
    simpa only [div_eq_mul_inv] using hr.aestronglyMeasurable.mul
      ((continuous_const.sub continuous_id).measurable.inv.aestronglyMeasurable)
  have hmeas' : AEStronglyMeasurable (fun s : ℝ => -r s / (x - s) ^ 2) := by
    simpa only [div_eq_mul_inv] using hr.aestronglyMeasurable.neg.mul
      (((continuous_const.sub continuous_id).pow 2).measurable.inv.aestronglyMeasurable)
  have hbound : ∀ᵐ s : ℝ, ∀ u ∈ ball x ((1 - |x|) / 2),
      ‖-r s / (u - s) ^ 2‖ ≤ ‖r s‖ / (((1 - |x|) / 2) ^ 2) := by
    filter_upwards [hzero] with s hs u hu
    by_cases hsi : s ∈ Ioo (-1 : ℝ) 1
    · simp [hs hsi]
    · rw [norm_div, norm_neg, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      apply div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hε 2)
      exact pow_le_pow_left₀ hε.le (exterior_gap_le_abs_sub hx hu hsi) 2
  have hdiff : ∀ᵐ s : ℝ, ∀ u ∈ ball x ((1 - |x|) / 2),
      HasDerivAt (fun u : ℝ => r s / (u - s)) (-r s / (u - s) ^ 2) u := by
    filter_upwards [hzero] with s hs u hu
    by_cases hsi : s ∈ Ioo (-1 : ℝ) 1
    · simp only [hs hsi, zero_div, neg_zero]
      exact hasDerivAt_const u 0
    · have hne : u - s ≠ 0 :=
        abs_pos.1 (hε.trans_le (exterior_gap_le_abs_sub hx hu hsi))
      convert (hasDerivAt_const u (r s)).div ((hasDerivAt_id u).sub_const s) hne using 1
      simp only [id_eq]
      ring
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le hε
    (Eventually.of_forall hmeas)
    (by simpa only [pow_one] using integrable_exterior_div_pow hr hzero hx 1)
    hmeas' hbound (hr.norm.div_const _) hdiff
  simpa only [neg_div, integral_neg] using hi.2

/-- The actual first exterior resolvent is C¹ on the source-free interval. -/
theorem contDiffOn_integral_exterior_div {r : ℝ → ℝ} (hr : Integrable r)
    (hzero : ∀ᵐ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → r s = 0) :
    ContDiffOn ℝ 1 (fun x : ℝ => ∫ s : ℝ, r s / (x - s)) (Ioo (-1 : ℝ) 1) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun x hx => (hasDerivAt_integral_exterior_div hr hzero (abs_lt.2 hx)).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  apply contDiffOn_zero.2
  have heq : EqOn (_root_.deriv (fun x : ℝ => ∫ s : ℝ, r s / (x - s)))
      (fun x : ℝ => -(∫ s : ℝ, r s / (x - s) ^ 2)) (Ioo (-1 : ℝ) 1) :=
    fun x hx => (hasDerivAt_integral_exterior_div hr hzero (abs_lt.2 hx)).deriv
  apply (continuousOn_congr heq).2
  intro x hx
  exact (continuousAt_integral_exterior_div_pow hr hzero (abs_lt.2 hx) 2).neg.continuousWithinAt

/-- A genuine core test has a uniform strict gap from both endpoints. -/
theorem IsCore.exists_support_radius {ψ : ℝ → ℝ} (hψ : IsCore ψ) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧ ∀ x ∈ tsupport ψ, |x| ≤ R := by
  by_cases hne : (tsupport ψ).Nonempty
  · obtain ⟨x, hx, hmax⟩ := hψ.2.1.exists_isMaxOn hne continuous_abs.continuousOn
    have hx1 : |x| < 1 := abs_lt.2 (hψ.2.2 hx)
    refine ⟨(|x| + 1) / 2, by positivity, by linarith, ?_⟩
    intro y hy
    have hxy : |y| ≤ |x| := hmax hy
    linarith
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    exact fun x hx => (hne ⟨x, hx⟩).elim

private theorem exterior_damped_pairing_deriv {r ψ : ℝ → ℝ}
    (hψ : IsCore ψ) (y ξ : ℝ) :
    (dampedSignMultiplier y ξ * fourier r ξ * star (fourier (_root_.deriv ψ) ξ)).re =
      Real.exp (-y * |ξ|) * (|ξ| * (fourier r ξ * star (fourier ψ ξ)).re) := by
  rw [fourier_deriv hψ.memRestrictedFormDomain.integrable (hψ.1.differentiable (by simp))
    hψ.deriv.memRestrictedFormDomain.integrable]
  unfold dampedSignMultiplier
  by_cases hξ : 0 < ξ
  · rw [if_pos hξ, abs_of_pos hξ]
    simp only [map_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    have heq : (Real.exp (-y * ξ) : ℂ) * Complex.I * fourier r ξ *
        ((ξ : ℂ) * -Complex.I * star (fourier ψ ξ)) =
        (Real.exp (-y * ξ) : ℂ) * (ξ : ℂ) * (fourier r ξ * star (fourier ψ ξ)) := by
      ring_nf
      simp only [Complex.I_sq]
      ring
    simp only [Complex.star_def] at heq
    rw [heq]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    ring
  · rw [if_neg hξ, abs_of_nonpos (le_of_not_gt hξ)]
    simp only [map_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    have heq : (Real.exp (-y * -ξ) : ℂ) * -Complex.I * fourier r ξ *
        ((ξ : ℂ) * -Complex.I * star (fourier ψ ξ)) =
        (Real.exp (-y * -ξ) : ℂ) * (-ξ : ℂ) * (fourier r ξ * star (fourier ψ ξ)) := by
      ring_nf
      simp only [Complex.I_sq]
      ring
    simp only [Complex.star_def] at heq
    rw [heq]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    ring

/-- The actual damped energy against a smooth test equals its ordinary
full-line conjugate-Poisson pairing. -/
theorem damped_energy_eq_real_kernel_pairing {r ψ : ℝ → ℝ}
    (hr : Integrable r) (hψ : IsCore ψ) {y : ℝ} (hy : 0 < y) :
    (1 / (2 * Real.pi)) * ∫ ξ : ℝ,
      Real.exp (-y * |ξ|) * |ξ| * (fourier r ξ * star (fourier ψ ξ)).re =
      ∫ x : ℝ, _root_.deriv ψ x * ∫ s : ℝ, r s *
        (-(x - s) / (Real.pi * ((x - s) ^ 2 + y ^ 2))) := by
  have hdi := hψ.deriv.memRestrictedFormDomain.integrable
  have h := damped_hilbert_fourier_pairing hr hdi hy
  have hre := congrArg Complex.re h
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  have hire : (∫ ξ : ℝ, dampedSignMultiplier y ξ * fourier r ξ *
      star (fourier (_root_.deriv ψ) ξ)).re = ∫ ξ : ℝ,
      (dampedSignMultiplier y ξ * fourier r ξ * star (fourier (_root_.deriv ψ) ξ)).re :=
    (integral_re (integrable_dampedSignMultiplier_fourier_pairing hr hdi hy)).symm
  rw [hire] at hre
  simp_rw [exterior_damped_pairing_deriv hψ] at hre
  simpa only [mul_assoc] using hre

private def exteriorKernelPair (r : ℝ → ℝ) (y x : ℝ) : ℝ :=
  ∫ s : ℝ, r s * (-(x - s) / (Real.pi * ((x - s) ^ 2 + y ^ 2)))

private theorem exterior_scalar_kernel_bound {a δ : ℝ} (hδ : 0 < δ) (ha : δ ≤ |a|)
    (y : ℝ) : ‖-a / (Real.pi * (a ^ 2 + y ^ 2))‖ ≤ 1 / (Real.pi * δ) := by
  have ha0 : 0 < |a| := hδ.trans_le ha
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero (abs_pos.1 ha0)
  have hd : 0 < a ^ 2 + y ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_neg, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hd]
  apply (div_le_div_iff₀ (mul_pos Real.pi_pos hd) (mul_pos Real.pi_pos hδ)).2
  have hmul : |a| * δ ≤ a ^ 2 := by
    have h := mul_le_mul_of_nonneg_left ha (abs_nonneg a)
    nlinarith [sq_abs a]
  calc
    |a| * (Real.pi * δ) = Real.pi * (|a| * δ) := by ring
    _ ≤ Real.pi * a ^ 2 := mul_le_mul_of_nonneg_left hmul Real.pi_pos.le
    _ ≤ 1 * (Real.pi * (a ^ 2 + y ^ 2)) := by
      nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg y)]

private theorem exteriorKernelPair_bound {r : ℝ → ℝ} (hr : Integrable r)
    (hzero : ∀ᵐ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → r s = 0)
    {R x : ℝ} (hR : R < 1) (hx : |x| ≤ R) (y : ℝ) :
    ‖exteriorKernelPair r y x‖ ≤ (∫ s : ℝ, ‖r s‖) / (Real.pi * (1 - R)) := by
  have hδ : 0 < 1 - R := by linarith
  unfold exteriorKernelPair
  have hbound : ∀ᵐ s : ℝ,
      ‖r s * (-(x - s) / (Real.pi * ((x - s) ^ 2 + y ^ 2)))‖ ≤
        ‖r s‖ / (Real.pi * (1 - R)) := by
    filter_upwards [hzero] with s hs
    by_cases hsi : s ∈ Ioo (-1 : ℝ) 1
    · simp [hs hsi]
    · have hsabs : 1 ≤ |s| := le_of_not_gt (fun h => hsi (abs_lt.1 h))
      have hd : 1 - R ≤ |x - s| := by
        have h := abs_sub_abs_le_abs_sub s x
        rw [abs_sub_comm s x] at h
        linarith
      rw [norm_mul]
      simpa only [one_div, div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left (exterior_scalar_kernel_bound hδ hd y) (norm_nonneg (r s))
  have hI := norm_integral_le_of_norm_le (hr.norm.div_const (Real.pi * (1 - R))) hbound
  simpa only [integral_div] using hI

private theorem exteriorKernelPair_measurable {r : ℝ → ℝ} (hr : Integrable r) (y : ℝ) :
    AEStronglyMeasurable (exteriorKernelPair r y) := by
  have hk : Measurable (fun p : ℝ × ℝ =>
      -(p.1 - p.2) / (Real.pi * ((p.1 - p.2) ^ 2 + y ^ 2))) :=
    (measurable_fst.sub measurable_snd).neg.div
      (measurable_const.mul (((measurable_fst.sub measurable_snd).pow_const 2).add measurable_const))
  exact (hr.aestronglyMeasurable.snd.mul hk.aestronglyMeasurable).integral_prod_right'

private theorem exteriorKernelPair_continuousAt_zero {r : ℝ → ℝ} (hr : Integrable r)
    (hzero : ∀ᵐ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → r s = 0)
    {x : ℝ} (hx : |x| < 1) : ContinuousAt (fun y : ℝ => exteriorKernelPair r y x) 0 := by
  have hδ : 0 < 1 - |x| := by linarith
  apply continuousAt_of_dominated
    (bound := fun s : ℝ => ‖r s‖ / (Real.pi * (1 - |x|)))
  · exact Eventually.of_forall fun y => hr.aestronglyMeasurable.mul
      ((measurable_const.sub measurable_id).neg.div
        (measurable_const.mul (((measurable_const.sub measurable_id).pow_const 2).add measurable_const))).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      filter_upwards [hzero] with s hs
      by_cases hsi : s ∈ Ioo (-1 : ℝ) 1
      · simp [hs hsi]
      · have hsabs : 1 ≤ |s| := le_of_not_gt (fun h => hsi (abs_lt.1 h))
        have hd : 1 - |x| ≤ |x - s| := by
          have h := abs_sub_abs_le_abs_sub s x
          rw [abs_sub_comm s x] at h
          linarith
        rw [norm_mul]
        simpa only [one_div, div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left (exterior_scalar_kernel_bound hδ hd y) (norm_nonneg (r s))
  · exact hr.norm.div_const _
  · filter_upwards [hzero] with s hs
    by_cases hsi : s ∈ Ioo (-1 : ℝ) 1
    · simp only [hs hsi, zero_mul]
      exact continuousAt_const
    · have hne : x - s ≠ 0 := by
        intro hz
        exact hsi (by simpa only [sub_eq_zero.1 hz] using abs_lt.1 hx)
      apply continuousAt_const.mul
      apply continuousAt_const.div
      · exact continuousAt_const.mul (continuousAt_const.add (continuousAt_id.pow 2))
      · simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
        exact mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hne)

/-- The ordinary conjugate-kernel pairing is continuous down to the axis
when the datum and the smooth test have genuinely separated supports. -/
theorem exterior_kernel_pairing_continuousAt_zero {r ψ : ℝ → ℝ}
    (hr : Integrable r) (hzero : ∀ᵐ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → r s = 0)
    (hψ : IsCore ψ) :
    ContinuousAt (fun y : ℝ => ∫ x : ℝ, _root_.deriv ψ x * exteriorKernelPair r y x) 0 := by
  obtain ⟨R, _, hR1, hR⟩ := hψ.exists_support_radius
  have hδ : 0 < 1 - R := by linarith
  have hdi := hψ.deriv.memRestrictedFormDomain.integrable
  have hsupp : tsupport (_root_.deriv ψ) ⊆ tsupport ψ :=
    closure_minimal support_deriv_subset (isClosed_tsupport ψ)
  apply continuousAt_of_dominated
    (bound := fun x : ℝ => ‖_root_.deriv ψ x‖ * ((∫ s : ℝ, ‖r s‖) / (Real.pi * (1 - R))))
  · exact Eventually.of_forall fun y =>
      hdi.aestronglyMeasurable.mul (exteriorKernelPair_measurable hr y)
  · exact Eventually.of_forall fun y => ae_of_all _ fun x => by
      by_cases hx : x ∈ tsupport (_root_.deriv ψ)
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (exteriorKernelPair_bound hr hzero hR1 (hR x (hsupp hx)) y) (norm_nonneg _)
      · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero, le_refl]
  · exact hdi.norm.mul_const _
  · exact ae_of_all _ fun x => by
      by_cases hx : x ∈ tsupport (_root_.deriv ψ)
      · exact continuousAt_const.mul (exteriorKernelPair_continuousAt_zero hr hzero
          ((hR x (hsupp hx)).trans_lt hR1))
      · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
        exact continuousAt_const

private theorem exteriorKernelPair_zero (r : ℝ → ℝ) (x : ℝ) :
    exteriorKernelPair r 0 x = -(1 / Real.pi) * ∫ s : ℝ, r s / (x - s) := by
  unfold exteriorKernelPair
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    by_cases hne : x - s = 0
    · simp [hne]
    · simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
      field_simp [Real.pi_ne_zero, hne]
      ring

/-- The original Fourier energy of integrable exterior data against a
genuine interior core test is its concrete separated-support kernel.
The formula is proved by removing damping and ordinary integration by
parts; no nonlocal-operator identification is a hypothesis. -/
theorem energy_eq_exterior_kernel_pairing {r ψ : ℝ → ℝ}
    (hr : Integrable r)
    (hzero : ∀ᵐ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → r s = 0)
    (hψ : IsCore ψ) :
    energy r ψ = -(1 / Real.pi) *
      (∫ x : ℝ, ψ x * (∫ s : ℝ, r s / (x - s) ^ 2)) := by
  have hlimE := damped_energy_tendsto_of_integrable_core hr hψ
  have hlimP := (exterior_kernel_pairing_continuousAt_zero hr hzero hψ).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have heq : (fun y : ℝ => (1 / (2 * Real.pi)) * ∫ ξ : ℝ,
      Real.exp (-y * |ξ|) * |ξ| * (fourier r ξ * star (fourier ψ ξ)).re) =ᶠ[𝓝[>] 0]
      (fun y : ℝ => ∫ x : ℝ, _root_.deriv ψ x * exteriorKernelPair r y x) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact damped_energy_eq_real_kernel_pairing hr hψ hy
  have hboundary : energy r ψ = ∫ x : ℝ, _root_.deriv ψ x * exteriorKernelPair r 0 x :=
    tendsto_nhds_unique hlimE (hlimP.congr' heq.symm)
  let H : ℝ → ℝ := fun x => -(1 / Real.pi) * ∫ s : ℝ, r s / (x - s)
  have hH : ContDiffOn ℝ 1 H (Ioo (-1 : ℝ) 1) :=
    contDiffOn_const.mul (contDiffOn_integral_exterior_div hr hzero)
  have hHd (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
      _root_.deriv H x = (1 / Real.pi) * ∫ s : ℝ, r s / (x - s) ^ 2 := by
    have hd := (hasDerivAt_integral_exterior_div hr hzero (abs_lt.2 hx)).const_mul (-(1 / Real.pi))
    convert hd.deriv using 1
    ring
  have hibp := integral_mul_deriv_eq_neg_deriv_mul_of_local_contDiff
    isOpen_Ioo hH hψ.1 hψ.2.1 hψ.2.2
  have hderiv : (fun x : ℝ => _root_.deriv H x * ψ x) =
      fun x : ℝ => (1 / Real.pi) * (ψ x * ∫ s : ℝ, r s / (x - s) ^ 2) := by
    funext x
    by_cases hx : x ∈ Ioo (-1 : ℝ) 1
    · rw [hHd x hx]
      ring
    · have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hψ.2.2 h))
      simp [hz]
  calc
    energy r ψ = ∫ x : ℝ, H x * _root_.deriv ψ x := by
      rw [hboundary]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only [H]
        rw [exteriorKernelPair_zero]
        ring
    _ = -(∫ x : ℝ, _root_.deriv H x * ψ x) := hibp
    _ = _ := by rw [hderiv, integral_const_mul]; ring

/-- Absolute integrability of the concrete separated double kernel,
so its two spatial integrations may genuinely be interchanged. -/
theorem integrable_exterior_double_kernel {r ψ : ℝ → ℝ} (hr : Integrable r)
    (hzero : ∀ᵐ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → r s = 0) (hψ : IsCore ψ) :
    Integrable (fun p : ℝ × ℝ => ψ p.1 * r p.2 / (p.1 - p.2) ^ 2)
      ((volume : Measure ℝ).prod volume) := by
  obtain ⟨R, _, hR1, hR⟩ := hψ.exists_support_radius
  have hδ : 0 < 1 - R := by linarith
  have hψi := hψ.memRestrictedFormDomain.integrable
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ψ p.1 * r p.2 / (p.1 - p.2) ^ 2)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [div_eq_mul_inv] using
      (hψi.aestronglyMeasurable.fst.mul hr.aestronglyMeasurable.snd).mul
        (((measurable_fst.sub measurable_snd).pow_const 2).inv.aestronglyMeasurable)
  apply ((hψi.norm.mul_prod hr.norm).div_const ((1 - R) ^ 2)).mono' hm
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hzero] with p hp
  by_cases hx : p.1 ∈ tsupport ψ
  · by_cases hs : p.2 ∈ Ioo (-1 : ℝ) 1
    · simp [hp hs]
    · have hsabs : 1 ≤ |p.2| := le_of_not_gt (fun h => hs (abs_lt.1 h))
      have hd : 1 - R ≤ |p.1 - p.2| := by
        have h := abs_sub_abs_le_abs_sub p.2 p.1
        rw [abs_sub_comm p.2 p.1] at h
        linarith [hR p.1 hx]
      simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (sq_pos_of_pos hδ) (pow_le_pow_left₀ hδ.le hd 2)
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- Fubini in the actual separated kernel, including its symmetry under
interchanging the interior and exterior variables. -/
theorem exterior_kernel_pairing_swap {r ψ : ℝ → ℝ} (hr : Integrable r)
    (hzero : ∀ᵐ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → r s = 0) (hψ : IsCore ψ) :
    (∫ x : ℝ, ψ x * ∫ s : ℝ, r s / (x - s) ^ 2) =
      ∫ s : ℝ, r s * ∫ x : ℝ, ψ x / (s - x) ^ 2 := by
  calc
    _ = ∫ x : ℝ, ∫ s : ℝ, ψ x * r s / (x - s) ^ 2 := by
      simp only [← integral_const_mul, mul_div_assoc]
    _ = ∫ s : ℝ, ∫ x : ℝ, ψ x * r s / (x - s) ^ 2 :=
      integral_integral_swap (integrable_exterior_double_kernel hr hzero hψ)
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun s => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          dsimp only
          have heq : (x - s) ^ 2 = (s - x) ^ 2 := by ring
          rw [heq]
          ring

/-- The exterior-source energy in the opposite Fubini order, ready for
limits of the actual interior core approximants. -/
theorem energy_eq_exterior_kernel_pairing_swap {r ψ : ℝ → ℝ} (hr : Integrable r)
    (hzero : ∀ᵐ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → r s = 0) (hψ : IsCore ψ) :
    energy r ψ = -(1 / Real.pi) *
      (∫ s : ℝ, r s * (∫ x : ℝ, ψ x / (s - x) ^ 2)) := by
  rw [energy_eq_exterior_kernel_pairing hr hzero hψ,
    exterior_kernel_pairing_swap hr hzero hψ]

end Torsion.Spectral

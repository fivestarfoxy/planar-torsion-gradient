import Torsion.CauchyTransformPoisson
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# The subtracted real Cauchy kernel

The real boundary value is an ordinary absolutely convergent integral after
symmetric subtraction.  The subtraction removes the singularity using the
actual Hölder estimate; no principal-value trace is assumed.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace Torsion.Spectral

/-- Symmetric subtraction of the real Cauchy kernel, also defined at height
zero.  At height zero the integrand is `(f (x+t)-f x)/t`. -/
def subtractedRealCauchy (f : ℝ → ℝ) (R : ℝ) (z : ℂ) : ℝ :=
  Real.pi⁻¹ * ∫ t in Icc (-R) R,
    t / (t ^ 2 + z.im ^ 2) * (f (z.re + t) - f z.re)

theorem subtractedRealCauchy_real (f : ℝ → ℝ) (R x : ℝ) :
    subtractedRealCauchy f R (x : ℂ) =
      Real.pi⁻¹ * ∫ t in Icc (-R) R, (f (x + t) - f x) / t := by
  unfold subtractedRealCauchy
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _
  by_cases ht : t = 0
  · simp [ht]
  · simp only [Complex.ofReal_im, Complex.ofReal_re, zero_pow (by norm_num : 2 ≠ 0), add_zero]
    field_simp
    ring

/-- The singular majorant needed for a positive Hölder exponent is locally
integrable on both sides of zero. -/
theorem integrableOn_abs_rpow {p R : ℝ} (hp : -1 < p) (hR : 0 ≤ R) :
    IntegrableOn (fun t : ℝ => |t| ^ p) (Icc (-R) R) := by
  have hpos : IntegrableOn (fun t : ℝ => |t| ^ p) (Icc 0 R) := by
    have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hR).1
      (intervalIntegral.intervalIntegrable_rpow' hp : IntervalIntegrable (fun t : ℝ => t ^ p) volume 0 R)
    apply hi.congr_fun _ measurableSet_Icc
    intro t ht
    dsimp
    rw [abs_of_nonneg ht.1]
  have hpos' : IntervalIntegrable (fun t : ℝ => |t| ^ p) volume 0 R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR).2 hpos
  have hneg : IntervalIntegrable (fun t : ℝ => |t| ^ p) volume (-R) 0 := by
    have h := IntervalIntegrable.iff_comp_neg.mp hpos'
    simpa only [neg_zero, abs_neg] using h.symm
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -R ≤ R)).1
    (hneg.trans hpos')

private theorem real_kernel_bound (t y d : ℝ) :
    ‖t / (t ^ 2 + y ^ 2) * d‖ ≤ ‖d / t‖ := by
  by_cases ht : t = 0
  · simp [ht]
  have htpos : 0 < |t| := abs_pos.2 ht
  have hden : 0 < t ^ 2 + y ^ 2 := by positivity
  rw [norm_mul, norm_div, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hden]
  have hk : |t| / (t ^ 2 + y ^ 2) ≤ 1 / |t| := by
    apply (div_le_div_iff₀ hden htpos).2
    nlinarith [sq_abs t, sq_nonneg y]
  simpa only [one_div, div_eq_mul_inv, Real.norm_eq_abs, mul_one, mul_comm] using
    mul_le_mul_of_nonneg_right hk (norm_nonneg d)

private theorem holder_quotient_bound {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (x t : ℝ) (ht : t ≠ 0) :
    ‖(f (x + t) - f x) / t‖ ≤ (C : ℝ) * |t| ^ ((α : ℝ) - 1) := by
  have h := hf.dist_le (x + t) x
  simp only [Real.dist_eq, add_sub_cancel_left] at h
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    |f (x + t) - f x| / |t| ≤ (C : ℝ) * |t| ^ (α : ℝ) / |t| :=
      div_le_div_of_nonneg_right h (abs_nonneg t)
    _ = (C : ℝ) * |t| ^ ((α : ℝ) - 1) := by
      rw [Real.rpow_sub (abs_pos.2 ht), Real.rpow_one, mul_div_assoc]

/-- Symmetric subtraction gives an absolutely convergent integral under the
actual global Hölder bound. The bound is uniform in horizontal position and
in height, including height zero. -/
theorem subtractedRealCauchy_integrable {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α) {R : ℝ} (hR : 0 ≤ R) (z : ℂ) :
    IntegrableOn (fun t : ℝ =>
      t / (t ^ 2 + z.im ^ 2) * (f (z.re + t) - f z.re)) (Icc (-R) R) := by
  have hcont := hf.continuous hα
  have hmeas : Measurable (fun t : ℝ =>
      t / (t ^ 2 + z.im ^ 2) * (f (z.re + t) - f z.re)) := by
    fun_prop
  apply ((integrableOn_abs_rpow (p := (α : ℝ) - 1) (by simpa using sub_lt_sub_right (show (0 : ℝ) < α by exact_mod_cast hα) 1) hR).const_mul
    (C : ℝ)).mono' hmeas.aestronglyMeasurable
  filter_upwards [(by simpa using (countable_singleton (0 : ℝ)).ae_not_mem (volume.restrict (Icc (-R) R)) : ∀ᵐ t : ℝ ∂volume.restrict (Icc (-R) R), t ≠ 0)] with t ht
  exact (real_kernel_bound t z.im _).trans (holder_quotient_bound hf z.re t ht)

/-- The regularized real Cauchy kernel has a jointly continuous extension
through the real line. The proof uses the integrable Hölder majorant, rather
than asserting a boundary trace. -/
theorem subtractedRealCauchy_continuous {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α) {R : ℝ} (hR : 0 ≤ R) :
    Continuous (subtractedRealCauchy f R) := by
  have hcont := hf.continuous hα
  apply continuous_const.mul
  apply continuous_of_dominated
    (bound := fun t : ℝ => (C : ℝ) * |t| ^ ((α : ℝ) - 1))
  · intro z
    exact (subtractedRealCauchy_integrable hf hα hR z).aestronglyMeasurable
  · intro z
    filter_upwards [(by simpa using (countable_singleton (0 : ℝ)).ae_not_mem (volume.restrict (Icc (-R) R)) : ∀ᵐ t : ℝ ∂volume.restrict (Icc (-R) R), t ≠ 0)] with t ht
    exact (real_kernel_bound t z.im _).trans (holder_quotient_bound hf z.re t ht)
  · exact (integrableOn_abs_rpow (p := (α : ℝ) - 1)
      (by simpa using sub_lt_sub_right (show (0 : ℝ) < α by exact_mod_cast hα) 1) hR).const_mul (C : ℝ)
  · filter_upwards [(by simpa using (countable_singleton (0 : ℝ)).ae_not_mem (volume.restrict (Icc (-R) R)) : ∀ᵐ t : ℝ ∂volume.restrict (Icc (-R) R), t ≠ 0)] with t ht
    have hden (z : ℂ) : t ^ 2 + z.im ^ 2 ≠ 0 := ne_of_gt (by positivity)
    exact ((continuous_const.div
      (continuous_const.add (Complex.continuous_im.pow 2)) hden).mul
        ((hcont.comp (Complex.continuous_re.add continuous_const)).sub
          (hcont.comp Complex.continuous_re)))

private theorem real_denominator_ne_zero {z : ℂ} (hz : z ∈ upperHalfPlane) (s : ℝ) :
    z - (s : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
  exact hz.ne' hi

/-- The real part of the actual Cauchy integral is the conjugate-Poisson
kernel, with the sign determined by the convention `-1/π`. -/
theorem realCauchy_re_eq_kernel {f : ℝ → ℝ} (hf : Continuous f)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (realCauchy f z).re = Real.pi⁻¹ * ∫ s in Icc (-1 : ℝ) 1,
      (s - z.re) / ((s - z.re) ^ 2 + z.im ^ 2) * f s := by
  have hfc : Continuous (fun s : ℝ => (f s : ℂ)) := Complex.continuous_ofReal.comp hf
  have hint : IntegrableOn (fun s : ℝ => (f s : ℂ) / (z - (s : ℂ)))
      (Icc (-1 : ℝ) 1) :=
    (hfc.div (continuous_const.sub Complex.continuous_ofReal)
      (real_denominator_ne_zero hz)).integrableOn_Icc
  unfold realCauchy
  rw [← integral_const_mul, ← integral_const_mul]
  have hre : (∫ s in Icc (-1 : ℝ) 1, -((Real.pi : ℂ)⁻¹) *
      ((f s : ℂ) / (z - (s : ℂ)))).re =
      ∫ s in Icc (-1 : ℝ) 1,
        (-((Real.pi : ℂ)⁻¹) * ((f s : ℂ) / (z - (s : ℂ)))).re :=
    (integral_re (hint.const_mul (-((Real.pi : ℂ)⁻¹)))).symm
  rw [hre]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s _
  rw [← Complex.ofReal_inv, ← Complex.ofReal_neg]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.div_re,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply, zero_mul, sub_zero,
    zero_add, zero_div]
  have hd : (z.re - s) ^ 2 + z.im ^ 2 = (s - z.re) ^ 2 + z.im ^ 2 := by ring
  simp only [← pow_two, add_zero]
  rw [hd]
  ring

private theorem integral_odd_real_kernel (R y : ℝ) :
    (∫ t in Icc (-R) R, t / (t ^ 2 + y ^ 2)) = 0 := by
  rw [integral_Icc_eq_integral_Ioc]
  by_cases hR : 0 ≤ R
  · rw [← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
    have h := intervalIntegral.integral_comp_neg (fun t : ℝ => t / (t ^ 2 + y ^ 2))
      (a := -R) (b := R)
    simp only [neg_neg, neg_sq, neg_div, intervalIntegral.integral_neg] at h
    linarith
  · have hempty : Ioc (-R) R = ∅ := Ioc_eq_empty_of_le (by linarith)
    simp [hempty]

/-- Symmetric subtraction is an exact identity for the interior real Cauchy
transform when the symmetric interval covers the support. -/
theorem realCauchy_re_eq_subtracted {f : ℝ → ℝ} (hf : Continuous f)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) {R : ℝ} (hR : 1 + |z.re| ≤ R) :
    (realCauchy f z).re = subtractedRealCauchy f R z := by
  have hR0 : 0 ≤ R := by linarith [abs_nonneg z.re]
  let k : ℝ → ℝ := fun s =>
    (s - z.re) / ((s - z.re) ^ 2 + z.im ^ 2) * f s
  have hsmall : (∫ s in Icc (-1 : ℝ) 1, k s) = ∫ s : ℝ, k s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    have habs : 1 ≤ |s| := by
      by_contra! h
      exact hs (abs_le.1 h.le)
    simp [k, hzero s habs]
  have hlarge : (∫ s in Icc (z.re - R) (z.re + R), k s) = ∫ s : ℝ, k s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    have habs : 1 ≤ |s| := by
      by_contra! h
      apply hs
      have hh := abs_lt.1 h
      constructor <;> linarith [le_abs_self z.re, neg_le_abs z.re]
    simp [k, hzero s habs]
  have hshift :
      (∫ t in Icc (-R) R, t / (t ^ 2 + z.im ^ 2) * f (z.re + t)) =
        ∫ s in Icc (z.re - R) (z.re + R), k s := by
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -R ≤ R),
      ← intervalIntegral.integral_of_le (by linarith : z.re - R ≤ z.re + R)]
    simpa [k, sub_eq_add_neg, add_assoc] using
      intervalIntegral.integral_comp_add_left k z.re (a := -R) (b := R)
  have hden (t : ℝ) : t ^ 2 + z.im ^ 2 ≠ 0 := ne_of_gt (by have : 0 < z.im := hz; positivity)
  have hk : Continuous (fun t : ℝ => t / (t ^ 2 + z.im ^ 2)) :=
    continuous_id.div ((continuous_id.pow 2).add continuous_const) hden
  have hsub :
      (∫ t in Icc (-R) R, t / (t ^ 2 + z.im ^ 2) * (f (z.re + t) - f z.re)) =
        ∫ t in Icc (-R) R, t / (t ^ 2 + z.im ^ 2) * f (z.re + t) := by
    simp_rw [mul_sub]
    have hi1 : IntegrableOn (fun t : ℝ => t / (t ^ 2 + z.im ^ 2) * f (z.re + t))
        (Icc (-R) R) := (hk.mul (hf.comp (continuous_const.add continuous_id))).integrableOn_Icc
    have hi2 : IntegrableOn (fun t : ℝ => t / (t ^ 2 + z.im ^ 2) * f z.re)
        (Icc (-R) R) := (hk.mul continuous_const).integrableOn_Icc
    rw [integral_sub hi1 hi2, integral_mul_const,
      integral_odd_real_kernel, zero_mul, sub_zero]
  rw [realCauchy_re_eq_kernel hf hz]
  change Real.pi⁻¹ * (∫ s in Icc (-1 : ℝ) 1, k s) = _
  rw [hsmall, ← hlarge, ← hshift]
  exact congrArg (fun q : ℝ => Real.pi⁻¹ * q) hsub.symm

/-- An explicit, absolutely convergent real boundary trace. The radius
`|x|+2` only ensures that the symmetric integration interval covers support. -/
def realCauchyBoundaryRe (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  subtractedRealCauchy f (|x| + 2) (x : ℂ)

/-- The real part of the actual Cauchy integral converges to the subtracted
integral. This establishes the real vertical boundary trace, rather than
taking a principal-value limit as a hypothesis. -/
theorem realCauchy_re_vertical_boundary {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) (x : ℝ) :
    Tendsto (fun c : ℝ => (realCauchy f ((x : ℂ) + (c⁻¹ : ℝ) * Complex.I)).re)
      atTop (𝓝 (realCauchyBoundaryRe f x)) := by
  have hpath : Tendsto (fun c : ℝ => (x : ℂ) + (c⁻¹ : ℝ) * Complex.I) atTop (𝓝 (x : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa using (tendsto_const_nhds.add (h.mul_const Complex.I))
  have hcont := subtractedRealCauchy_continuous hf hα (show 0 ≤ |x| + 2 by positivity)
  apply (hcont.continuousAt.tendsto.comp hpath).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  apply (realCauchy_re_eq_subtracted (hf.continuous hα) hzero
    (by simpa [upperHalfPlane] using inv_pos.2 hc) _).symm
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  linarith

/-- Any larger symmetric radius gives exactly the same boundary integral.
This follows from the actual interior identity and the proved boundary limit. -/
theorem subtractedRealCauchy_radius_independent {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) (x : ℝ)
    {R : ℝ} (hR : 1 + |x| ≤ R) :
    subtractedRealCauchy f R (x : ℂ) = realCauchyBoundaryRe f x := by
  have hpath : Tendsto (fun c : ℝ => (x : ℂ) + (c⁻¹ : ℝ) * Complex.I) atTop (𝓝 (x : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa using (tendsto_const_nhds.add (h.mul_const Complex.I))
  have hR0 : 0 ≤ R := by linarith [abs_nonneg x]
  have hlim := ((subtractedRealCauchy_continuous hf hα hR0).continuousAt.tendsto.comp hpath)
  have hlim' : Tendsto
      (fun c : ℝ => (realCauchy f ((x : ℂ) + (c⁻¹ : ℝ) * Complex.I)).re)
      atTop (𝓝 (subtractedRealCauchy f R (x : ℂ))) := by
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    apply (realCauchy_re_eq_subtracted (hf.continuous hα) hzero
      (by simpa [upperHalfPlane] using inv_pos.2 hc) _).symm
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero] using hR
  exact tendsto_nhds_unique hlim' (realCauchy_re_vertical_boundary hf hα hzero x)

/-- The real component of the Cauchy transform with its genuine Hilbert
trace on the real boundary. -/
def realCauchyReExtension (f : ℝ → ℝ) (z : ℂ) : ℝ :=
  if 0 < z.im then (realCauchy f z).re else realCauchyBoundaryRe f z.re

theorem realCauchyReExtension_eq_re {f : ℝ → ℝ} {z : ℂ}
    (hz : z ∈ upperHalfPlane) : realCauchyReExtension f z = (realCauchy f z).re :=
  if_pos hz

theorem realCauchyReExtension_ofReal (f : ℝ → ℝ) (x : ℝ) :
    realCauchyReExtension f (x : ℂ) = realCauchyBoundaryRe f x := by
  simp [realCauchyReExtension]

theorem realCauchyReExtension_eq_subtracted {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) {z : ℂ} (hz : 0 ≤ z.im)
    {R : ℝ} (hR : 1 + |z.re| ≤ R) :
    realCauchyReExtension f z = subtractedRealCauchy f R z := by
  by_cases hp : 0 < z.im
  · rw [realCauchyReExtension, if_pos hp]
    exact realCauchy_re_eq_subtracted (hf.continuous hα) hzero hp hR
  · have hzi : z.im = 0 := le_antisymm (not_lt.mp hp) hz
    have hzeq : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hzi]
    rw [realCauchyReExtension, if_neg hp, hzeq]
    exact (subtractedRealCauchy_radius_independent hf hα hzero z.re hR).symm

/-- Hölder cancellation proves genuine joint continuity of the real
Cauchy trace on the entire closed upper half-plane. -/
theorem realCauchyReExtension_continuousOn {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) :
    ContinuousOn (realCauchyReExtension f) {z : ℂ | 0 ≤ z.im} := by
  intro z hz
  let R : ℝ := |z.re| + 3
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcont := (subtractedRealCauchy_continuous hf hα hR).continuousAt.continuousWithinAt
    (s := {w : ℂ | 0 ≤ w.im}) (x := z)
  apply hcont.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z zero_lt_one)] with w hw hball
    apply realCauchyReExtension_eq_subtracted hf hα hzero hw
    have hn : ‖w - z‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hball
    have hre : |w.re - z.re| < 1 := by
      simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (w - z)).trans_lt hn
    have ha : |w.re| ≤ |w.re - z.re| + |z.re| := by
      simpa only [sub_add_cancel] using abs_add (w.re - z.re) z.re
    dsimp [R]
    linarith
  · exact realCauchyReExtension_eq_subtracted hf hα hzero hz (by dsimp [R]; linarith)

theorem realCauchyReExtension_continuousOn_closure {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) :
    ContinuousOn (realCauchyReExtension f) (closure upperHalfPlane) := by
  apply (realCauchyReExtension_continuousOn hf hα hzero).mono
  refine closure_minimal ?_ (isClosed_le continuous_const Complex.continuous_im)
  intro z hz
  exact (show 0 < z.im from hz).le

end Torsion.Spectral



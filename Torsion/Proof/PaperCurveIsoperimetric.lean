module

public import Torsion.Proof.PaperRadialGreen
public import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section

/-! # Wirtinger's inequality and the signed area of a closed planar curve -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Torsion

private theorem interval_memLp_two {a b : ℝ} {f : ℝ → Plane} (hc : ContinuousOn f (Icc a b)) :
    MemLp f 2 (volume.restrict (Ioc a b)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  apply MemLp.of_bound ((hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) M
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hM t (Ioc_subset_Icc_self ht)

/-- Wirtinger's periodic inequality on an interval: every nonzero Fourier
frequency has modulus at least one, while the zero mode vanishes by centering. -/
theorem closedCurve_wirtinger {a b : ℝ} (hab : a < b) {f v : ℝ → Plane}
    (hc : ContinuousOn f (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (v t) t) (he : f a = f b)
    (hm : (∫ t in a..b, f t) = 0) :
    (∫ t in a..b, ‖f t‖ ^ 2) ≤ ((b - a) / (2 * Real.pi)) ^ 2 * ∫ t in a..b, ‖v t‖ ^ 2 := by
  let k := (b - a) / (2 * Real.pi)
  have hT := sub_pos.mpr hab
  have hi : IntervalIntegrable v volume a b := hv.intervalIntegrable_of_Icc hab.le
  have hcoeff (n : ℤ) : ‖fourierCoeffOn hab f n‖ ≤ k * ‖fourierCoeffOn hab v n‖ := by
    by_cases hn : n = 0
    · subst n
      have h0 := fourierCoeffOn_eq_integral f 0 hab
      simp only [neg_zero, fourier_zero, one_smul, hm, smul_zero] at h0
      rw [h0, norm_zero]
      dsimp [k]
      positivity
    have h := fourierCoeffOn_of_hasDerivAt_Ioo hab hn
      (show ContinuousOn f (uIcc a b) by simpa [uIcc_of_le hab.le] using hc)
      (fun t ht => hd t (by simpa [min_eq_left hab.le, max_eq_right hab.le] using ht)) hi
    rw [← he, sub_self, mul_zero, zero_sub, ← Complex.ofReal_sub] at h
    rw [h, norm_mul, norm_div, norm_one, norm_neg, norm_mul, norm_mul, norm_mul, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_intCast, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT, abs_of_pos Real.pi_pos]
    have habs : 1 ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast (show (1 : ℤ) ≤ |n| by have := abs_pos.mpr hn; omega)
    have height : 0 < 2 * Real.pi := by positivity
    norm_num only [norm_neg, Complex.norm_ofNat]
    dsimp [k]
    calc
      _ = ((b - a) / (2 * Real.pi) * ‖fourierCoeffOn hab v n‖) / |(n : ℝ)| := by ring
      _ ≤ _ := div_le_self (by positivity) habs
  have hweak : ∀ n : ℤ, ‖fourierCoeffOn hab f n‖ ^ 2 ≤
      k ^ 2 * ‖fourierCoeffOn hab v n‖ ^ 2 := fun n => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hcoeff n) 2
  have h := hasSum_le hweak (hasSum_sq_fourierCoeffOn hab (interval_memLp_two hc))
    ((hasSum_sq_fourierCoeffOn hab (interval_memLp_two hv)).mul_left (k ^ 2))
  simp only [smul_eq_mul] at h
  apply (mul_le_mul_iff_right₀ (inv_pos.mpr hT)).mp
  calc
    (b-a)⁻¹ * (∫ t in a..b, ‖f t‖ ^ 2) ≤ _ := h
    _ = _ := by dsimp [k]; ring

/-- On a closed planar curve, twice signed area is controlled by the integral
of its squared speed with sharp coefficient (b−a)/(2π). -/
theorem closedCurve_cross_le_energy {a b : ℝ} (hab : a < b) {γ v : ℝ → Plane}
    (hc : ContinuousOn γ (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt γ (v t) t) (hclosed : γ a = γ b) :
    (∫ t in a..b, planarCross (γ t) (v t)) ≤ (b-a)/(2*Real.pi) * ∫ t in a..b, ‖v t‖^2 := by
  let m : Plane := (b-a)⁻¹ • ∫ t in a..b, γ t
  let f (t : ℝ) := γ t - m
  let k := (b - a) / (2 * Real.pi)
  have hk : 0 < k := div_pos (sub_pos.mpr hab) (by positivity)
  have hfc : ContinuousOn f (Icc a b) := hc.sub continuousOn_const
  have hmean : (∫ t in a..b, f t) = 0 := by
    change (∫ t in a..b, γ t - m) = 0
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable_of_Icc hab.le) intervalIntegrable_const,
      intervalIntegral.integral_const]
    dsimp only [m]
    rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hab.ne'), one_smul, sub_self]
  have hw := closedCurve_wirtinger hab hfc hv (fun t ht => (hd t ht).sub_const m)
    (show f a = f b by dsimp [f]; rw [hclosed]) hmean
  have hi : IntervalIntegrable v volume a b := hv.intervalIntegrable_of_Icc hab.le
  have hzero : (∫ t in a..b, v t) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hc hd hi, hclosed, sub_self]
  have hcros {g : ℝ → Plane} (hg : ContinuousOn g (Icc a b)) :
      ContinuousOn (fun t => planarCross (g t) (v t)) (Icc a b) :=
    ((Complex.continuous_re.comp_continuousOn hg).mul (Complex.continuous_im.comp_continuousOn hv)).sub
      ((Complex.continuous_im.comp_continuousOn hg).mul (Complex.continuous_re.comp_continuousOn hv))
  have hconst : (∫ t in a..b, planarCross m (v t)) = 0 := by
    unfold planarCross
    rw [intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      ]
    · change m.re * (∫ t in a..b, Complex.imCLM (v t)) - m.im * (∫ t in a..b, Complex.reCLM (v t)) = 0
      rw [Complex.imCLM.intervalIntegral_comp_comm hi, Complex.reCLM.intervalIntegral_comp_comm hi, hzero]
      simp
    · exact (continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hv)).intervalIntegrable_of_Icc hab.le
    · exact (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hv)).intervalIntegrable_of_Icc hab.le
  have heq : (∫ t in a..b, planarCross (f t) (v t)) = ∫ t in a..b, planarCross (γ t) (v t) := by
    have he (t : ℝ) : planarCross (f t) (v t) = planarCross (γ t) (v t) - planarCross m (v t) := by
      simp only [f, planarCross, Complex.sub_re, Complex.sub_im]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_sub ((hcros hc).intervalIntegrable_of_Icc hab.le)
      ((hcros (g := fun _ => m) continuousOn_const).intervalIntegrable_of_Icc hab.le), hconst, sub_zero]
  have hineq : (∫ t in a..b, 2*k*planarCross (f t) (v t)) ≤
      ∫ t in a..b, ‖f t‖^2 + k^2*‖v t‖^2 := by
    apply intervalIntegral.integral_mono_on hab.le
      ((continuousOn_const.mul (hcros hfc)).intervalIntegrable_of_Icc hab.le)
      (((hfc.norm.pow 2).add (continuousOn_const.mul (hv.norm.pow 2))).intervalIntegrable_of_Icc hab.le)
    intro t _
    change 2*k*planarCross (f t) (v t) ≤ ‖f t‖^2 + k^2*‖v t‖^2
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, planarCross]
    nlinarith [sq_nonneg ((f t).re - k * (v t).im), sq_nonneg ((f t).im + k * (v t).re)]
  rw [intervalIntegral.integral_const_mul, heq, intervalIntegral.integral_add (f := fun t => ‖f t‖^2) (g := fun t => k^2 * ‖v t‖^2)
    ((hfc.norm.pow 2).intervalIntegrable_of_Icc hab.le)
    ((continuousOn_const.mul (hv.norm.pow 2)).intervalIntegrable_of_Icc hab.le),
    intervalIntegral.integral_const_mul] at hineq
  change _ ≤ k^2 * _ at hw
  apply (mul_le_mul_iff_right₀ (show 0 < 2*k by positivity)).mp
  change 2*k*_ ≤ 2*k*(k*_)
  nlinarith only [hineq, hw]

end Torsion

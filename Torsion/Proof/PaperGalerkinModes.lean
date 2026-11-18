module

public import Torsion.Proof.PaperGalerkin
public import Torsion.RestrictedSpectralSemicircleWeak
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial

@[expose] public section

/-! # The Hilbert transform of the zero-exterior Galerkin modes

In the upper half-plane a power of the explicit semicircle branch is a
bounded holomorphic function with precisely the sine mode as its imaginary
trace. The real boundary value determines the restricted half-Laplacian. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal
namespace Torsion.Galerkin
open Spectral Polynomial.Chebyshev

def trialMode (k : ℕ) (x : ℝ) : ℝ :=
  semicircleBarrier x * (U ℝ ((k : ℤ) - 1)).eval x

theorem trialMode_zero_exterior (k : ℕ) (x : ℝ) (hx : 1 ≤ |x|) : trialMode k x = 0 := by
  simp [trialMode, semicircleBarrier_zero_exterior x hx]

theorem trialMode_sine (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    trialMode k x = Real.sin ((k : ℝ) * Real.arccos x) := by
  simpa only [trialMode, semicircleBarrier_eq_sqrt, Int.cast_natCast] using
    chebyshevSine (k : ℤ) (abs_le.mp hx).1 (abs_le.mp hx).2

/-- Polynomial multiples of the zero-exterior semicircle retain its endpoint
Hölder exponent. Clamping the real coordinate gives a globally bounded map. -/
theorem semicircle_polynomial_holder (p : Polynomial ℝ) :
    ∃ C : ℝ≥0, HolderWith C (1 / 2) (fun x => semicircleBarrier x * p.eval x) := by
  let clip (x : ℝ) := min (max x (-1)) 1
  let v (x : ℝ) := (clip x, semicircleBarrier x)
  let S : Set (ℝ × ℝ) := Icc (-1) 1 ×ˢ Icc 0 1
  let F (z : ℝ × ℝ) := z.2 * p.eval z.1
  have hs : Convex ℝ S := (convex_Icc _ _).prod (convex_Icc _ _)
  have hc : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hd : ContDiff ℝ 1 (fun x => p.eval x) := by simpa using p.contDiff_aeval (𝕜 := ℝ) 1
  have hF : ContDiff ℝ 1 F := contDiff_snd.mul (hd.comp contDiff_fst)
  obtain ⟨K, hK⟩ := hF.contDiffOn.exists_lipschitzOnWith (by simp) hs hc
  have hclip (x : ℝ) : clip x ∈ Icc (-1 : ℝ) 1 :=
    ⟨le_min (le_max_right _ _) (by norm_num), min_le_right _ _⟩
  have hv (x : ℝ) : v x ∈ S := ⟨hclip _, semicircleBarrier_nonneg _, semicircleBarrier_le_one _⟩
  have hev (x : ℝ) : F (v x) = semicircleBarrier x * p.eval x := by
    by_cases hx : |x| ≤ 1
    · simp [F, v, clip, max_eq_left (abs_le.mp hx).1, min_eq_left (abs_le.mp hx).2]
    · simp [F, v, semicircleBarrier_zero_exterior x (le_of_not_ge hx)]
  have hL : LipschitzWith 1 clip := by
    simpa [clip] using (LipschitzWith.id.max (LipschitzWith.const (-1 : ℝ))).min
      (LipschitzWith.const (1 : ℝ))
  refine ⟨K * 2, holderWith_of_dist_bound fun x y => ?_⟩
  rw [← hev x, ← hev y]
  norm_num only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one]
  rw [← Real.sqrt_eq_rpow]
  apply (hK.dist_le_mul (v x) (hv x) (v y) (hv y)).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  change max (dist (clip x) (clip y)) (dist (semicircleBarrier x) (semicircleBarrier y)) ≤ _
  apply max_le
  · have ha := hL.dist_le_mul x y
    simp only [NNReal.coe_one, one_mul] at ha
    have hb : dist (clip x) (clip y) ≤ 2 := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [(hclip x).1,(hclip x).2,(hclip y).1,(hclip y).2]
    have hsq := Real.sq_sqrt (dist_nonneg (x:=x) (y:=y))
    nlinarith [dist_nonneg (x:=clip x) (y:=clip y), Real.sqrt_nonneg (dist x y),
      mul_le_mul_of_nonneg_left hb (dist_nonneg (x:=clip x) (y:=clip y))]
  · have h := semicircleBarrier_holder_half.dist_le x y
    simpa only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one, Real.sqrt_eq_rpow] using h

def modeExtension (k : ℕ) (z : ℂ) : ℂ := - ((-semicircleComplex z) ^ k)

theorem modeExtension_diffContOnCl (k : ℕ) : DiffContOnCl ℂ (modeExtension k) upperHalfPlane :=
  ⟨(semicircleComplex_differentiableOn.neg.pow k).neg,
    ((semicircleComplex_continuous.neg.pow k).neg).continuousOn⟩

theorem modeExtension_norm_le_one (k : ℕ) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    ‖modeExtension k z‖ ≤ 1 := by
  simp only [modeExtension, norm_neg, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (semicircleComplex_norm_le_one hz)

private theorem modeExtension_on_interval (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    modeExtension k x = -Complex.exp (-(k : ℂ) * (Real.arccos x : ℂ) * Complex.I) := by
  have he : -semicircleComplex (x : ℂ) = Complex.exp ((-(Real.arccos x : ℝ) : ℂ) * Complex.I) := by
    rw [semicircleComplex, semicircleRoot_ofReal_interior hx, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I]
    apply Complex.ext <;> simp [Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2, Real.sin_arccos]
  simp only [modeExtension, he, ← Complex.exp_nat_mul]
  congr 2
  ring

theorem modeExtension_im (k : ℕ) (x : ℝ) : (modeExtension k x).im = trialMode k x := by
  by_cases hx : |x| ≤ 1
  · rw [modeExtension_on_interval k hx, trialMode_sine k hx]
    rw [show -(k : ℂ) * (Real.arccos x : ℂ) = ((-((k:ℝ)*Real.arccos x):ℝ):ℂ) by push_cast; ring]
    rw [Complex.neg_im, Complex.exp_ofReal_mul_I_im, Real.sin_neg, neg_neg]
  · have h := semicircleComplex_boundary_im x
    rw [semicircleBarrier_zero_exterior x (le_of_not_ge hx)] at h
    have he : semicircleComplex x = ((semicircleComplex x).re : ℂ) := Complex.ext rfl (by simpa using h)
    rw [trialMode_zero_exterior k x (le_of_not_ge hx)]
    rw [modeExtension, he, ← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_neg, Complex.ofReal_im]

theorem modeExtension_re (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    (modeExtension k x).re = -(T ℝ (k : ℤ)).eval x := by
  rw [modeExtension_on_interval k hx]
  rw [show -(k : ℂ) * (Real.arccos x : ℂ) = ((-((k:ℝ)*Real.arccos x):ℝ):ℂ) by push_cast; ring]
  have h := T_real_cos (Real.arccos x) (k : ℤ)
  rw [Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2] at h
  rw [Complex.neg_re, Complex.exp_ofReal_mul_I_re, Real.cos_neg, h]
  push_cast
  rfl

theorem trialMode_cauchyExtension (k : ℕ) (hk : 0 < k) :
    EqOn (realCauchyExtension (trialMode k)) (modeExtension k) (closure upperHalfPlane) := by
  obtain ⟨C, hm⟩ := semicircle_polynomial_holder (U ℝ ((k : ℤ)-1))
  change HolderWith C (1 / 2) (trialMode k) at hm
  have hz := trialMode_zero_exterior k
  have hc := hm.continuous (by norm_num)
  have hα : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hV := realCauchyExtension_diffContOnCl hm hα
    hz
  obtain ⟨B, _, hB⟩ := realCauchy_exists_norm_bound hm hα
    hz
  let H : ℂ → ℂ := fun z => realCauchyExtension (trialMode k) z - (modeExtension k) z
  have hd : DiffContOnCl ℂ H upperHalfPlane := hV.sub (modeExtension_diffContOnCl k)
  have hb (z : ℂ) (hzU : z ∈ upperHalfPlane) : ‖H z‖ ≤ B + 1 := by
    dsimp only [H]
    apply (norm_sub_le _ _).trans
    rw [realCauchyExtension_eq hc hz hzU]
    linarith [hB z hzU, (modeExtension_norm_le_one k) hzU]
  have hr (x : ℝ) : (H (x : ℂ)).im = 0 := by
    simp only [H, Complex.sub_im, realCauchyExtension_ofReal,
      modeExtension_im]
    simp
  let zseq : ℕ → ℂ := fun n => (n : ℂ) * Complex.I
  have hseq : ∀ᶠ n in atTop, zseq n ∈ upperHalfPlane := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    simpa only [zseq, upperHalfPlane, mem_ofPred_eq, Complex.mul_im,
      Complex.natCast_re, Complex.I_im, mul_one, Complex.natCast_im,
      Complex.I_re, mul_zero, add_zero] using hp
  have hn : Tendsto (fun n : ℕ => ‖zseq n‖) atTop atTop := by
    simpa only [zseq, norm_mul, Complex.norm_natCast, Complex.norm_I, mul_one] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hC : Tendsto (fun n => realCauchy (trialMode k) (zseq n)) atTop (𝓝 0) := by
    have h := (cauchy_integral_tendsto_zero
      (Complex.continuous_ofReal.comp hc).continuousOn hn).const_mul
        (-((Real.pi : ℂ)⁻¹))
    simpa only [realCauchy, mul_zero, Function.comp_apply] using! h
  have hVlim : Tendsto (fun n => realCauchyExtension (trialMode k) (zseq n)) atTop (𝓝 0) := by
    apply hC.congr'
    filter_upwards [hseq] with n hn
    exact (realCauchyExtension_eq hc hz hn).symm
  have hdecay : Tendsto (fun y : ℝ => modeExtension k ((y : ℂ) * Complex.I)) atTop (𝓝 0) := by
    simpa [modeExtension, zero_pow hk.ne'] using (semicircleComplex_tendsto_imaginary_ray.neg.pow k).neg
  have hU : Tendsto (fun n => (modeExtension k) (zseq n)) atTop (𝓝 0) := by
    simpa only [zseq, Complex.ofReal_natCast, Function.comp_apply] using!
      hdecay.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hlim : Tendsto (fun n => H (zseq n)) atTop (𝓝 0) := by
    simpa only [H, sub_zero] using hVlim.sub hU
  have hzero := bounded_holomorphic_real_boundary_eq_zero hd (B + 1) hb hr hseq hlim
  have heq : EqOn (realCauchyExtension (trialMode k)) (modeExtension k) upperHalfPlane :=
    fun z hz => sub_eq_zero.mp (hzero z hz)
  exact heq.of_subset_closure hV.continuousOn (modeExtension_diffContOnCl k).continuousOn
    subset_closure Subset.rfl


/-- The real Cauchy trace is minus the first-kind Chebyshev polynomial.
The Hilbert-transform convention of the paper has the opposite sign. -/
theorem trialMode_cauchyBoundary (k : ℕ) (hk : 0 < k) {x : ℝ} (hx : |x| < 1) :
    realCauchyBoundaryRe (trialMode k) x = -(T ℝ (k : ℤ)).eval x := by
  have he := congrArg Complex.re
    (trialMode_cauchyExtension k hk (ofReal_mem_closure_upperHalfPlane x))
  rw [realCauchyExtension_ofReal, modeExtension_re k hx.le] at he
  simpa [Complex.mul_re] using he

/-- The Hilbert derivative of the zero-exterior mode is the claimed
restricted half-Laplacian at every interior point. -/
theorem trialMode_hilbertDerivative (k : ℕ) (hk : 0 < k) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun t => -realCauchyBoundaryRe (trialMode k) t)
      ((k : ℝ) * (U ℝ ((k : ℤ) - 1)).eval x) x := by
  have heq : (fun t => -realCauchyBoundaryRe (trialMode k) t) =ᶠ[𝓝 x]
      fun t => (T ℝ (k : ℤ)).eval t := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with t ht
    simp only [trialMode_cauchyBoundary k hk ht, neg_neg]
  have hd := (T ℝ (k : ℤ)).hasDerivAt x
  rw [T_derivative_eq_U] at hd
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  simpa using hd

end Torsion.Galerkin

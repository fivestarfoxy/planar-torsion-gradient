import Torsion.RestrictedSpectralSemicircleComplex
import Torsion.RestrictedSpectralSemicircleAdmission
import Torsion.RestrictedSpectralBoundaryPrimitive
import Torsion.RestrictedSpectralWeakPrimitive
import Torsion.CauchyTransformImageBound
import Torsion.CauchyTransformUniqueness

/-!
# The actual weak equation of the semicircle barrier

Bounded holomorphic uniqueness identifies the genuine Cauchy integral with
the explicit square-root branch. Its real boundary value is `-x` inside the
interval. The proved Fourier/Cauchy test pairing then gives `|D|b = 1` in
the original weak form, first on the core and then on the entire closed form.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion.Spectral

theorem realCauchyExtension_semicircle :
    EqOn (realCauchyExtension semicircleBarrier) semicircleComplex (closure upperHalfPlane) := by
  have hα : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hV := realCauchyExtension_diffContOnCl semicircleBarrier_holder_half hα
    semicircleBarrier_zero_exterior
  obtain ⟨B, _, hB⟩ := realCauchy_exists_norm_bound semicircleBarrier_holder_half hα
    semicircleBarrier_zero_exterior
  let H : ℂ → ℂ := fun z => realCauchyExtension semicircleBarrier z - semicircleComplex z
  have hd : DiffContOnCl ℂ H upperHalfPlane := hV.sub semicircleComplex_diffContOnCl
  have hb (z : ℂ) (hz : z ∈ upperHalfPlane) : ‖H z‖ ≤ B + 1 := by
    dsimp only [H]
    apply (norm_sub_le _ _).trans
    rw [realCauchyExtension_eq semicircleBarrier_continuous semicircleBarrier_zero_exterior hz]
    linarith [hB z hz, semicircleComplex_norm_le_one hz]
  have hr (x : ℝ) : (H (x : ℂ)).im = 0 := by
    simp only [H, Complex.sub_im, realCauchyExtension_ofReal,
      semicircleComplex_boundary_im]
    simp
  let zseq : ℕ → ℂ := fun n => (n : ℂ) * Complex.I
  have hseq : ∀ᶠ n in atTop, zseq n ∈ upperHalfPlane := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    simpa only [zseq, upperHalfPlane, mem_setOf_eq, Complex.mul_im,
      Complex.natCast_re, Complex.I_im, mul_one, Complex.natCast_im,
      Complex.I_re, mul_zero, add_zero] using hp
  have hn : Tendsto (fun n : ℕ => ‖zseq n‖) atTop atTop := by
    simpa only [zseq, norm_mul, Complex.norm_natCast, Complex.norm_I, mul_one] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hC : Tendsto (fun n => realCauchy semicircleBarrier (zseq n)) atTop (𝓝 0) := by
    have h := (cauchy_integral_tendsto_zero
      (Complex.continuous_ofReal.comp semicircleBarrier_continuous).continuousOn hn).const_mul
        (-((Real.pi : ℂ)⁻¹))
    simpa only [realCauchy, mul_zero] using h
  have hVlim : Tendsto (fun n => realCauchyExtension semicircleBarrier (zseq n)) atTop (𝓝 0) := by
    apply hC.congr'
    filter_upwards [hseq] with n hn
    exact (realCauchyExtension_eq semicircleBarrier_continuous semicircleBarrier_zero_exterior hn).symm
  have hU : Tendsto (fun n => semicircleComplex (zseq n)) atTop (𝓝 0) := by
    simpa only [zseq, Complex.ofReal_natCast] using
      semicircleComplex_tendsto_imaginary_ray.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hlim : Tendsto (fun n => H (zseq n)) atTop (𝓝 0) := by
    simpa only [H, sub_zero] using hVlim.sub hU
  have hzero := bounded_holomorphic_real_boundary_eq_zero hd (B + 1) hb hr hseq hlim
  have heq : EqOn (realCauchyExtension semicircleBarrier) semicircleComplex upperHalfPlane :=
    fun z hz => sub_eq_zero.mp (hzero z hz)
  exact heq.of_subset_closure hV.continuousOn semicircleComplex_continuous.continuousOn
    subset_closure Subset.rfl

theorem realCauchyBoundaryRe_semicircle {x : ℝ} (hx : |x| < 1) :
    realCauchyBoundaryRe semicircleBarrier x = -x := by
  have h := congrArg Complex.re
    (realCauchyExtension_semicircle (ofReal_mem_closure_upperHalfPlane x))
  simpa only [realCauchyExtension_ofReal, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero, semicircleComplex_boundary_re hx] using h

theorem semicircleBarrier_core_equation (ψ : ℝ → ℝ) (hψ : IsCore ψ) :
    energy semicircleBarrier ψ = ∫ x : ℝ, ψ x := by
  rw [energy_eq_realCauchyBoundary_deriv_pairing semicircleBarrier_holder_half
    (by norm_num : (0 : ℝ≥0) < 1 / 2) semicircleBarrier_zero_exterior
    semicircleBarrier_memRestrictedFormDomain.2.1 hψ]
  have heq : (∫ x : ℝ, deriv ψ x * realCauchyBoundaryRe semicircleBarrier x) =
      ∫ x : ℝ, (-x) * deriv ψ x := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      by_cases hx : x ∈ Ioo (-1 : ℝ) 1
      · rw [realCauchyBoundaryRe_semicircle (abs_lt.2 hx)]
        ring
      · have hz : deriv ψ x = 0 :=
          image_eq_zero_of_nmem_tsupport (fun h => hx (hψ.deriv.2.2 h))
        rw [hz]
        ring
  rw [heq]
  have hdψ := hψ.1.differentiable (by simp)
  have hi1 : Integrable (fun x : ℝ => (-x) * deriv ψ x) :=
    (continuous_id.neg.mul hψ.deriv.1.continuous).integrable_of_hasCompactSupport hψ.deriv.2.1.mul_left
  have hi2 : Integrable (fun x : ℝ => (-1 : ℝ) * ψ x) :=
    (hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1).const_mul (-1)
  have hi3 : Integrable (fun x : ℝ => (-x) * ψ x) :=
    (continuous_id.neg.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x : ℝ => (hasDerivAt_id x).neg) (fun x => (hdψ x).hasDerivAt) hi1 hi2 hi3
  simpa only [Pi.mul_apply, neg_one_mul, integral_neg, neg_neg] using h

theorem semicircleBarrier_weak_equation (ψ : ℝ → ℝ) (hψ : MemRestrictedFormDomain ψ) :
    energy semicircleBarrier ψ = ∫ x : ℝ, ψ x := by
  obtain ⟨v, hv, hL, hE⟩ := hψ.2.2.2
  have hvI (n : ℕ) : Integrable (v n) := (hv n).memRestrictedFormDomain.integrable
  have hvE (n : ℕ) : FiniteEnergy (v n) := (hv n).memRestrictedFormDomain.2.1
  let V : ℕ → Lp ℂ 2 (volume : Measure ℝ) := fun n => halfDerivative (v n) (hvI n) (hvE n)
  let F : Lp ℂ 2 (volume : Measure ℝ) := halfDerivative ψ hψ.integrable hψ.2.1
  have hnorm : Tendsto (fun n => ‖V n - F‖ ^ 2) atTop (𝓝 0) := by
    have h := hE.const_mul (2 * Real.pi)
    convert h using 1
    · funext n
      rw [energy_sub_eq_norm_halfDerivative_sub (hvI n) hψ.integrable (hvE n) hψ.2.1]
      dsimp only [V, F]
      field_simp
    · simp
  have hV : Tendsto V atTop (𝓝 F) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hnorm
  have henergy : Tendsto (fun n => energy semicircleBarrier (v n)) atTop
      (𝓝 (energy semicircleBarrier ψ)) := by
    let B : Lp ℂ 2 (volume : Measure ℝ) := halfDerivative semicircleBarrier
      semicircleBarrier_integrable semicircleBarrier_memRestrictedFormDomain.2.1
    have hi : Tendsto (fun n => inner (𝕜 := ℝ) B (V n)) atTop (𝓝 (inner (𝕜 := ℝ) B F)) :=
      tendsto_const_nhds.inner hV
    have h := hi.const_mul (1 / (2 * Real.pi))
    simpa only [V, F, B, energy_eq_inner_halfDerivative semicircleBarrier_integrable (hvI _)
      semicircleBarrier_memRestrictedFormDomain.2.1 (hvE _),
      energy_eq_inner_halfDerivative semicircleBarrier_integrable hψ.integrable
        semicircleBarrier_memRestrictedFormDomain.2.1 hψ.2.1] using h
  have hL1 := tendsto_eLpNorm_one_of_two_zero_exterior
    (fun n => (hv n).memRestrictedFormDomain.1) hψ.1
    (fun n => (hv n).memRestrictedFormDomain.2.2.1) hψ.2.2.1 hL
  have hFourier := (tendstoUniformly_fourier_of_tendsto_eLpNorm_one hvI hψ.integrable hL1).tendsto_at 0
  have hIntegral : Tendsto (fun n => ∫ x : ℝ, v n x) atTop (𝓝 (∫ x : ℝ, ψ x)) := by
    have hr := Complex.continuous_re.continuousAt.tendsto.comp hFourier
    simpa only [fourier, mul_zero, zero_mul, Complex.ofReal_zero, neg_zero, Complex.exp_zero,
      one_mul, integral_complex_ofReal, Complex.ofReal_re, Function.comp_apply] using hr
  exact tendsto_nhds_unique
    (henergy.congr' (Eventually.of_forall fun n => semicircleBarrier_core_equation (v n) (hv n)))
    hIntegral

end Torsion.Spectral

module

public import Torsion.RestrictedSpectralCauchyMinimum
public import Torsion.RestrictedSpectralWeakCauchy
public import Torsion.RestrictedSpectralCauchyL1
public import Torsion.RestrictedSpectralOddKernelMinimum

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Strict pointwise positivity of the actual odd spectral representative

At a hypothetical positive-half zero, the actual analytic representative
vanishes quadratically. Dominated convergence computes the original
Cauchy double-pole boundary integral. The classical boundary ODE obtained
from the original weak eigenfunction equation forces this integral to
vanish, contradicting the strictly positive odd paired kernel.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- In the upper half of a genuine holomorphic continuation ball, its
second derivative is the actual original-density double-pole integral. -/
theorem MemRestrictedFormDomain.height_extension_second_derivative
    {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f)
    {x r : ℝ} {A : ℂ → ℂ}
    (hAeq : EqOn A (realCauchyExtension (height f))
      (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}))
    {z : ℂ} (hzball : z ∈ Metric.ball (x : ℂ) r) (hzH : z ∈ upperHalfPlane) :
    deriv (deriv A) z = -(Real.pi : ℂ)⁻¹ *
      ∫ s in Icc (-1 : ℝ) 1, (f s : ℂ) / (z - (s : ℂ)) ^ 2 := by
  have hHopen : IsOpen upperHalfPlane := isOpen_lt continuous_const Complex.continuous_im
  have hDpoint (w : ℂ) (hwb : w ∈ Metric.ball (x : ℂ) r) (hwH : w ∈ upperHalfPlane) :
      deriv A w = -realCauchy f w := by
    have heq : A =ᶠ[𝓝 w] cauchy f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hwb, hHopen.mem_nhds hwH] with v hvb hvH
      rw [hAeq ⟨hvb, (show 0 < v.im from hvH).le⟩, realCauchyExtension_eq hf.height_continuous
        (fun s hs => height_zero_of_one_le_abs f hs) hvH]
      rfl
    rw [heq.deriv_eq]
    exact hf.deriv_cauchy_eq_neg_realCauchy hodd hwH
  have heqD : deriv A =ᶠ[𝓝 z] fun w => -realCauchy f w := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzball, hHopen.mem_nhds hzH] with w hwb hwH
    exact hDpoint w hwb hwH
  rw [heqD.deriv_eq]
  simpa only [neg_mul, Pi.neg_apply] using!
    (hasDerivAt_realCauchy_of_integrable hf.integrable.integrableOn hzH).neg.deriv

/-- At a hypothetical nonnegative interior zero, the actual original
spectral double-pole integral must vanish by the analytically continued
Cauchy equation. No principal-value identification is assumed. -/
theorem IsRestrictedEigenfunction.integral_div_sq_eq_zero_of_regularEigenfunction_zero
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hzero : regularEigenfunction f x = 0) :
    (∫ s : ℝ, f s / (x - s) ^ 2) = 0 := by
  have hxfull : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hquot := hf.div_sq_integrable_of_regularEigenfunction_zero hodd hnonneg hx hzero
  obtain ⟨r, hr, A, hAd, hAeq, hAre⟩ :=
    hf.exists_height_Cauchy_extension_secondDerivative_re hodd x hxfull
  rw [hzero, mul_zero] at hAre
  let z : ℝ → ℂ := fun y => (x : ℂ) + (y : ℂ) * Complex.I
  have hz : Tendsto z (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have hy : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [z, zero_mul, add_zero] using tendsto_const_nhds.add (hy.mul_const Complex.I)
  have hzb : ∀ᶠ y : ℝ in 𝓝[>] 0, z y ∈ Metric.ball (x : ℂ) r :=
    hz.eventually (Metric.ball_mem_nhds (x : ℂ) hr)
  have hzH : ∀ᶠ y : ℝ in 𝓝[>] 0, z y ∈ upperHalfPlane := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa only [z, upperHalfPlane, mem_ofPred_eq, mem_Ioi, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
      zero_mul, add_zero, zero_add] using! hy
  have hAc : ContinuousAt (deriv (deriv A)) (x : ℂ) :=
    (((hAd.analyticOnNhd Metric.isOpen_ball).deriv.deriv) (x : ℂ)
      (Metric.mem_ball_self hr)).continuousAt
  have hlimA := hAc.tendsto.comp hz
  have hlimI := (cauchy_doublePole_vertical_tendsto hf.1.integrable.integrableOn hquot.integrableOn).const_mul
    (-(Real.pi : ℂ)⁻¹)
  have heq : (fun y : ℝ => -(Real.pi : ℂ)⁻¹ *
      ∫ s in Icc (-1 : ℝ) 1, (f s : ℂ) / (z y - (s : ℂ)) ^ 2) =ᶠ[𝓝[>] 0]
      (fun y => deriv (deriv A) (z y)) := by
    filter_upwards [hzb, hzH] with y hyb hyH
    exact (hf.1.height_extension_second_derivative hodd hAeq hyb hyH).symm
  have hvalue := tendsto_nhds_unique hlimA (hlimI.congr' heq)
  let I : ℝ := ∫ s in Icc (-1 : ℝ) 1, f s / (x - s) ^ 2
  have hrealform : -(Real.pi : ℂ)⁻¹ * (I : ℂ) = ((-Real.pi⁻¹ * I : ℝ) : ℂ) := by
    push_cast
    rfl
  change deriv (deriv A) (x : ℂ) = -(Real.pi : ℂ)⁻¹ * (I : ℂ) at hvalue
  rw [hrealform] at hvalue
  have hRe := congrArg Complex.re hvalue
  rw [hAre] at hRe
  simp only [Complex.ofReal_re] at hRe
  have hIzero : I = 0 := (mul_eq_zero.mp hRe.symm).resolve_left
    (neg_ne_zero.mpr (inv_ne_zero Real.pi_ne_zero))
  have hsupport : (∫ s in Icc (-1 : ℝ) 1, f s / (x - s) ^ 2) =
      ∫ s : ℝ, f s / (x - s) ^ 2 := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hf.1.2.2.1] with s hs hsout
    rw [hs (fun hsin => hsout (Ioo_subset_Icc_self hsin)), zero_div]
  exact hsupport.symm.trans hIzero

/-- Every nonzero odd weak eigenfunction with nonnegative positive-half
sign has a strictly positive analytic representative throughout the
positive interval. The proof uses the actual weak Cauchy equation and
the strictly positive paired half-line kernel. -/
theorem IsRestrictedEigenfunction.regularEigenfunction_pos
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f) :
    ∀ x ∈ Ioo (0 : ℝ) 1, 0 < regularEigenfunction f x := by
  have hpos : volume {s : ℝ | 0 < s ∧ 0 < f s} ≠ 0 := by
    intro hz
    have hnpos : ∀ᵐ s : ℝ ∂volume, ¬ (0 < s ∧ 0 < f s) := by
      simpa only [ae_iff, not_not] using hz
    have hzhalf : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
      filter_upwards [hnonneg, ae_restrict_of_ae hnpos,
        ae_restrict_mem measurableSet_Ioi] with s hn hnp hs
      change f s = 0
      exact le_antisymm (le_of_not_gt (fun hp => hnp ⟨hs, hp⟩)) hn
    exact hf.2.1 (ae_eq_zero_of_odd_ae_eq_zero_half hodd hzhalf)
  intro x hx
  have hn := hf.regularEigenfunction_nonneg hodd hnonneg x hx
  by_contra hnot
  have hz : regularEigenfunction f x = 0 := le_antisymm (le_of_not_gt hnot) hn
  have hi := hf.div_sq_integrable_of_regularEigenfunction_zero hodd hnonneg hx hz
  have hI0 := hf.integral_div_sq_eq_zero_of_regularEigenfunction_zero hodd hnonneg hx hz
  have hIp := integral_odd_quotient_sq_pos hx.1 hodd hnonneg hpos hi
  rw [hI0] at hIp
  exact lt_irrefl 0 hIp

end Torsion.Spectral

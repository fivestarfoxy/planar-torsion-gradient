module

public import Torsion.RestrictedSpectralWeakPrimitive
public import Torsion.CauchyTransformIntegrationByParts
public import Torsion.CauchyTransformPoisson

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual Cauchy integration by parts for weak odd spectral data

The original odd core approximants converge in actual L¹, as do their
integrated heights. Bounded Cauchy kernels at every positive height pass the
proved core integration-by-parts identity to the original form domain.
No continuity of the original density is required.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

private theorem complex_pairing_tendsto_of_integral_norm_sub
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hv : ∀ n, Integrable (v n)) (hf : Integrable f)
    (hlim : Tendsto (fun n => ∫ x : ℝ, ‖v n x - f x‖) atTop (𝓝 0))
    {k : ℝ → ℂ} (hk : Continuous k) {C : ℝ} (hC : ∀ x : ℝ, ‖k x‖ ≤ C) :
    Tendsto (fun n => ∫ x in Icc (-1 : ℝ) 1, k x * (v n x : ℂ)) atTop
      (𝓝 (∫ x in Icc (-1 : ℝ) 1, k x * (f x : ℂ))) := by
  have hC0 : 0 ≤ C := (norm_nonneg (k 0)).trans (hC 0)
  have hp {g : ℝ → ℝ} (hg : Integrable g) :
      Integrable (fun x => k x * (g x : ℂ)) := by
    have hgc : Integrable (fun x : ℝ => (g x : ℂ)) (volume : Measure ℝ) :=
      Complex.ofRealCLM.integrable_comp hg
    exact hgc.bdd_mul hk.aestronglyMeasurable (ae_of_all _ hC)
  have hbound (n : ℕ) :
      ‖(∫ x in Icc (-1 : ℝ) 1, k x * (v n x : ℂ)) -
        ∫ x in Icc (-1 : ℝ) 1, k x * (f x : ℂ)‖ ≤
          C * ∫ x : ℝ, ‖v n x - f x‖ := by
    rw [← integral_sub (hp (hv n)).integrableOn (hp hf).integrableOn]
    have h := norm_integral_le_of_norm_le
      (μ := volume.restrict (Icc (-1 : ℝ) 1))
      (((hv n).sub hf).norm.const_mul C).integrableOn
      (ae_of_all _ fun x => show ‖k x * (v n x : ℂ) - k x * (f x : ℂ)‖ ≤
        C * ‖v n x - f x‖ from by
          rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real]
          exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
    calc
      _ ≤ ∫ x in Icc (-1 : ℝ) 1, C * ‖v n x - f x‖ := h
      _ = C * ∫ x in Icc (-1 : ℝ) 1, ‖v n x - f x‖ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral ((hv n).sub hf).norm
          (ae_of_all _ fun x => norm_nonneg _)) hC0
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) hbound
    (by simpa only [mul_zero] using hlim.const_mul C)

private theorem inverse_cauchy_power_continuous {z : ℂ} (hz : z ∈ upperHalfPlane) (m : ℕ) :
    Continuous (fun x : ℝ => ((z - (x : ℂ)) ^ m)⁻¹) := by
  have hne (x : ℝ) : z - (x : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
    exact hz.ne' hi
  exact ((continuous_const.sub Complex.continuous_ofReal).pow m).inv₀
    (fun x => pow_ne_zero m (hne x))

private theorem inverse_cauchy_power_bound {z : ℂ} (hz : z ∈ upperHalfPlane) (m : ℕ) (x : ℝ) :
    ‖((z - (x : ℂ)) ^ m)⁻¹‖ ≤ (z.im ^ m)⁻¹ := by
  have hdist : z.im ≤ ‖z - (x : ℂ)‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using Complex.im_le_norm (z - (x : ℂ))
  rw [norm_inv, norm_pow]
  exact inv_anti₀ (pow_pos hz m) (pow_le_pow_left₀ hz.le hdist m)

/-- The actual Cauchy height kernel obeys integration by parts for every
odd original restricted form member, without datum continuity. -/
theorem MemRestrictedFormDomain.cauchy_height_integrationByParts {φ : ℝ → ℝ}
    (hφ : MemRestrictedFormDomain φ) (hodd : Function.Odd φ)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (∫ s in Icc (-1 : ℝ) 1, (height φ s : ℂ) / (z - (s : ℂ)) ^ 2) =
      ∫ s in Icc (-1 : ℝ) 1, (φ s : ℂ) / (z - (s : ℂ)) := by
  obtain ⟨v, hv, hL, _, _⟩ := hφ.exists_odd_core_approximation hodd
  have hvL (n : ℕ) : MemLp (v n) 2 volume := (hv n).1.memRestrictedFormDomain.1
  have hvI (n : ℕ) : Integrable (v n) := (hv n).1.memRestrictedFormDomain.integrable
  have hvzero (n : ℕ) : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0 :=
    (hv n).1.memRestrictedFormDomain.2.2.1
  have hL1 := tendsto_eLpNorm_one_of_two_zero_exterior hvL hφ.1 hvzero hφ.2.2.1 hL
  have hdata := integral_norm_sub_tendsto_of_eLpNorm_one hvI hφ.integrable hL1
  have hheight := integral_norm_height_sub_tendsto hvL hφ.1 hvI hφ.integrable hL1
  have hleft : Tendsto
      (fun n => ∫ s in Icc (-1 : ℝ) 1, (height (v n) s : ℂ) / (z - (s : ℂ)) ^ 2)
      atTop (𝓝 (∫ s in Icc (-1 : ℝ) 1, (height φ s : ℂ) / (z - (s : ℂ)) ^ 2)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      complex_pairing_tendsto_of_integral_norm_sub
        (fun n => height_integrable_of_memLp (hvL n)) hφ.height_integrable hheight
        (inverse_cauchy_power_continuous hz 2) (inverse_cauchy_power_bound hz 2)
  have hright : Tendsto
      (fun n => ∫ s in Icc (-1 : ℝ) 1, (v n s : ℂ) / (z - (s : ℂ)))
      atTop (𝓝 (∫ s in Icc (-1 : ℝ) 1, (φ s : ℂ) / (z - (s : ℂ)))) := by
    simpa only [pow_one, div_eq_mul_inv, mul_comm] using
      complex_pairing_tendsto_of_integral_norm_sub hvI hφ.integrable hdata
        (inverse_cauchy_power_continuous hz 1) (inverse_cauchy_power_bound hz 1)
  have heq (n : ℕ) :
      (∫ s in Icc (-1 : ℝ) 1, (height (v n) s : ℂ) / (z - (s : ℂ)) ^ 2) =
        ∫ s in Icc (-1 : ℝ) 1, (v n s : ℂ) / (z - (s : ℂ)) :=
    Torsion.Spectral.cauchy_height_integrationByParts (hv n).1.1.continuous (hv n).2
      ((hv n).1.memRestrictedFormDomain.zero_exterior (hv n).1.1.continuous) hz
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall fun n => (heq n).symm))

/-- Holomorphy and the actual derivative kernel for a weak spectral
height require continuity only of its already proved integrated profile. -/
theorem MemRestrictedFormDomain.hasDerivAt_cauchy {φ : ℝ → ℝ}
    (hφ : MemRestrictedFormDomain φ) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasDerivAt (cauchy φ)
      ((Real.pi : ℂ)⁻¹ *
        ∫ s in Icc (-1 : ℝ) 1, (height φ s : ℂ) / (z - (s : ℂ)) ^ 2) z := by
  have hc : ContinuousOn (fun s : ℝ => (height φ s : ℂ)) (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp hφ.height_continuous).continuousOn
  simpa only [cauchy, neg_div, integral_neg, neg_mul_neg] using!
    (hasDerivAt_cauchy_integral hc hz).const_mul (-((Real.pi : ℂ)⁻¹))

/-- The decisive actual weak-data Cauchy identity, with the sign and
normalization of the original construction. -/
theorem MemRestrictedFormDomain.deriv_cauchy_eq_neg_realCauchy {φ : ℝ → ℝ}
    (hφ : MemRestrictedFormDomain φ) (hodd : Function.Odd φ)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    deriv (cauchy φ) z = -realCauchy φ z := by
  rw [(hφ.hasDerivAt_cauchy hz).deriv, hφ.cauchy_height_integrationByParts hodd hz]
  simp only [realCauchy, neg_mul, neg_neg]

end Torsion.Spectral

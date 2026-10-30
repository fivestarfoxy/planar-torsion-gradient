import Torsion.RestrictedSpectralOddCore
import Torsion.RestrictedSpectralHeightRegularity
import Torsion.RestrictedSpectralFourierContinuity
import Torsion.RestrictedSpectralPairingContinuity

/-!
# The concrete odd primitive without continuity of its datum

Odd core approximation and the bounded actual height integral operator
extend the Fourier primitive identity to the original closed form domain.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform

namespace Torsion.Spectral

/-- The original height integral is linear on integrable data. -/
theorem height_sub_of_integrable {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    height (fun x => f x - g x) = fun x => height f x - height g x := by
  funext x
  by_cases hx : |x| < 1
  · simp only [height, if_pos hx]
    exact integral_sub hf.integrableOn hg.integrableOn
  · simp only [height, if_neg hx, sub_self]

/-- Uniform bound for the actual height difference by its datum's actual
L¹ difference. -/
theorem norm_height_sub_le_integral_norm {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    ‖height f x - height g x‖ ≤ ∫ s : ℝ, ‖f s - g s‖ := by
  rw [← congrFun (height_sub_of_integrable hf hg) x]
  by_cases hx : |x| < 1
  · simp only [height, if_pos hx]
    exact (norm_integral_le_integral_norm _).trans
      (setIntegral_le_integral (hf.sub hg).norm (ae_of_all _ fun s => norm_nonneg _))
  · simp only [height, if_neg hx, norm_zero]
    exact integral_nonneg fun s => norm_nonneg _

/-- The height operator is bounded from actual L¹ differences to actual
L¹ differences, on the integrable L² data used here. -/
theorem integral_norm_height_sub_le {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hfi : Integrable f) (hgi : Integrable g) :
    (∫ x : ℝ, ‖height f x - height g x‖) ≤ 2 * ∫ x : ℝ, ‖f x - g x‖ := by
  let D : ℝ := ∫ x : ℝ, ‖f x - g x‖
  have hD : 0 ≤ D := integral_nonneg fun x => norm_nonneg _
  have hH : Integrable (fun x => ‖height f x - height g x‖) :=
    ((height_integrable_of_memLp hf).sub (height_integrable_of_memLp hg)).norm
  have hB : Integrable ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => D)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc
  have hpoint (x : ℝ) : ‖height f x - height g x‖ ≤
      (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => D) x := by
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · simpa only [indicator_of_mem hx, D] using norm_height_sub_le_integral_norm hfi hgi x
    · have hx' : ¬ |x| < 1 := fun h => hx (abs_le.1 h.le)
      simp only [height, if_neg hx', sub_self, norm_zero, indicator_of_not_mem hx, le_refl]
  have h := integral_mono hH hB hpoint
  rw [integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at h
  simpa only [smul_eq_mul, show (1 - (-1 : ℝ)) = 2 by norm_num, D] using h

/-- Conversion from actual L¹ seminorm convergence to convergence of the
ordinary real norm integrals. -/
theorem integral_norm_sub_tendsto_of_eLpNorm_one
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hvi : ∀ n, Integrable (v n)) (hfi : Integrable f)
    (hlim : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 1 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : ℝ, ‖v n x - f x‖) atTop (𝓝 0) := by
  have htoReal := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hlim
  have heq (n : ℕ) : (∫ x : ℝ, ‖v n x - f x‖) =
      (eLpNorm (fun x => v n x - f x) 1 volume).toReal := by
    simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using
      integral_norm_eq_lintegral_enorm ((hvi n).aestronglyMeasurable.sub hfi.aestronglyMeasurable)
  simp_rw [heq]
  exact htoReal

/-- Actual L¹ datum convergence gives actual L¹ convergence of the height. -/
theorem integral_norm_height_sub_tendsto
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hv : ∀ n, MemLp (v n) 2 volume) (hf : MemLp f 2 volume)
    (hvi : ∀ n, Integrable (v n)) (hfi : Integrable f)
    (hlim : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 1 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : ℝ, ‖height (v n) x - height f x‖) atTop (𝓝 0) := by
  have hreal := integral_norm_sub_tendsto_of_eLpNorm_one hvi hfi hlim
  have hupper : Tendsto (fun n => 2 * ∫ x : ℝ, ‖v n x - f x‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hreal.const_mul 2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => integral_nonneg fun x => norm_nonneg _)
    (fun n => integral_norm_height_sub_le (hv n) hf (hvi n) hfi)

/-- Pointwise convergence of the original Fourier transform of the height. -/
theorem fourier_height_tendsto_of_tendsto_eLpNorm_one
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hv : ∀ n, MemLp (v n) 2 volume) (hf : MemLp f 2 volume)
    (hvi : ∀ n, Integrable (v n)) (hfi : Integrable f)
    (hlim : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 1 volume) atTop (𝓝 0)) (ξ : ℝ) :
    Tendsto (fun n => fourier (height (v n)) ξ) atTop (𝓝 (fourier (height f) ξ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (integral_norm_height_sub_tendsto hv hf hvi hfi hlim)
    (fun n => norm_nonneg _)
    (fun n => norm_fourier_sub_le_integral_norm (height_integrable_of_memLp (hv n))
      (height_integrable_of_memLp hf) ξ)

/-- The concrete Fourier primitive identity on the actual closed restricted
form domain needs no continuity of the eigenfunction or other datum. -/
theorem MemRestrictedFormDomain.fourier_height_identity {φ : ℝ → ℝ}
    (hφ : MemRestrictedFormDomain φ) (hodd : Function.Odd φ) (ξ : ℝ) :
    fourier φ ξ = -(ξ : ℂ) * Complex.I * fourier (height φ) ξ := by
  obtain ⟨v, hv, hL, _, _⟩ := hφ.exists_odd_core_approximation hodd
  have hvL (n : ℕ) : MemLp (v n) 2 volume := (hv n).1.memRestrictedFormDomain.1
  have hvI (n : ℕ) : Integrable (v n) := (hv n).1.memRestrictedFormDomain.integrable
  have hvzero (n : ℕ) : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0 :=
    (hv n).1.memRestrictedFormDomain.2.2.1
  have hL1 := tendsto_eLpNorm_one_of_two_zero_exterior hvL hφ.1 hvzero hφ.2.2.1 hL
  have hF := (tendstoUniformly_fourier_of_tendsto_eLpNorm_one hvI hφ.integrable hL1).tendsto_at ξ
  have hH := (fourier_height_tendsto_of_tendsto_eLpNorm_one hvL hφ.1 hvI hφ.integrable hL1 ξ).const_mul
    (-(ξ : ℂ) * Complex.I)
  have heq (n : ℕ) : fourier (v n) ξ = -(ξ : ℂ) * Complex.I * fourier (height (v n)) ξ :=
    Torsion.Spectral.fourier_height_identity (hv n).1.1.continuous (hv n).2
      ((hv n).1.memRestrictedFormDomain.zero_exterior (hv n).1.1.continuous) ξ
  apply tendsto_nhds_unique hF
  exact hH.congr' (Eventually.of_forall fun n => (heq n).symm)

/-- Integrating an actual odd form member preserves finite half energy,
without any continuity hypothesis on the datum. -/
theorem MemRestrictedFormDomain.finiteEnergy_height {φ : ℝ → ℝ}
    (hφ : MemRestrictedFormDomain φ) (hodd : Function.Odd φ) :
    FiniteEnergy (height φ) := by
  let g : ℝ → ℝ := fun ξ => |ξ| * ‖fourier (height φ) ξ‖ ^ 2
  have hg : Continuous g := continuous_abs.mul
    ((fourier_continuous hφ.height_integrable).norm.pow 2)
  have hnear : IntegrableOn g (Icc (-1 : ℝ) 1) := hg.integrableOn_Icc
  have hfar : IntegrableOn g (Icc (-1 : ℝ) 1)ᶜ := by
    apply hφ.2.1.integrableOn.mono' hg.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with ξ hξ
    have hξabs : 1 ≤ |ξ| := by
      by_contra h
      have hlt : |ξ| < 1 := lt_of_not_ge h
      exact hξ (abs_le.mp hlt.le)
    have hnorm : ‖fourier φ ξ‖ = |ξ| * ‖fourier (height φ) ξ‖ := by
      rw [hφ.fourier_height_identity hodd]
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hle : ‖fourier (height φ) ξ‖ ≤ ‖fourier φ ξ‖ := by
      rw [hnorm]
      exact le_mul_of_one_le_left (norm_nonneg _) hξabs
    change ‖|ξ| * ‖fourier (height φ) ξ‖ ^ 2‖ ≤ |ξ| * ‖fourier φ ξ‖ ^ 2
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hle 2) (abs_nonneg _)
  have hall := hnear.union hfar
  simpa only [union_compl_self, integrableOn_univ] using hall

/-- The original Fourier form commutes with taking the actual odd
primitive, for every actual closed form member. -/
theorem MemRestrictedFormDomain.energy_height_deriv {φ ψ : ℝ → ℝ}
    (hφ : MemRestrictedFormDomain φ) (hodd : Function.Odd φ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    energy (height φ) (deriv ψ) = energy φ ψ := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hdi : Integrable (deriv ψ) := hdc.integrable_of_hasCompactSupport hc.deriv
  unfold energy
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    dsimp only
    rw [fourier_deriv (hψ.continuous.integrable_of_hasCompactSupport hc) hd hdi,
      hφ.fourier_height_identity hodd]
    congr 2
    simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I, neg_mul, mul_neg]
    ring

/-- Weak integration by parts for the actual primitive of every odd
restricted form member, without pointwise regularity of the datum. -/
theorem MemRestrictedFormDomain.integral_height_mul_deriv {φ ψ : ℝ → ℝ}
    (hφ : MemRestrictedFormDomain φ) (hodd : Function.Odd φ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ x : ℝ, height φ x * deriv ψ x) = ∫ x : ℝ, φ x * ψ x := by
  obtain ⟨v, hv, hL, _, _⟩ := hφ.exists_odd_core_approximation hodd
  have hvL (n : ℕ) : MemLp (v n) 2 volume := (hv n).1.memRestrictedFormDomain.1
  have hvI (n : ℕ) : Integrable (v n) := (hv n).1.memRestrictedFormDomain.integrable
  have hvzero (n : ℕ) : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0 :=
    (hv n).1.memRestrictedFormDomain.2.2.1
  have hL1 := tendsto_eLpNorm_one_of_two_zero_exterior hvL hφ.1 hvzero hφ.2.2.1 hL
  have hreal := integral_norm_sub_tendsto_of_eLpNorm_one hvI hφ.integrable hL1
  have hHreal := integral_norm_height_sub_tendsto hvL hφ.1 hvI hφ.integrable hL1
  have hleft := integral_mul_tendsto_of_integral_norm_sub hφ.height_integrable
    (fun n => height_integrable_of_memLp (hvL n)) hHreal
    (hψ.continuous_deriv (by simp)) hc.deriv
  have hright := integral_mul_tendsto_of_integral_norm_sub hφ.integrable hvI hreal hψ.continuous hc
  have heq (n : ℕ) : (∫ x : ℝ, height (v n) x * deriv ψ x) = ∫ x : ℝ, v n x * ψ x :=
    Torsion.Spectral.integral_height_mul_deriv (hv n).1.1.continuous (hv n).2
      ((hv n).1.memRestrictedFormDomain.zero_exterior (hv n).1.1.continuous) hψ hc
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Eventually.of_forall fun n => (heq n).symm)

/-- The derivative of the integrated weak spectral distribution vanishes,
using only oddness of the actual weak eigenfunction. -/
theorem IsRestrictedEigenfunction.height_derivative_equation_of_odd
    {a : ℝ} {φ : ℝ → ℝ} (hEig : IsRestrictedEigenfunction a φ) (hodd : Function.Odd φ)
    {ψ : ℝ → ℝ} (hψ : IsCore ψ) :
    energy (height φ) (deriv ψ) =
      a * ∫ x : ℝ, height φ x * deriv ψ x := by
  rw [hEig.1.energy_height_deriv hodd hψ.1 hψ.2.1,
    hEig.1.integral_height_mul_deriv hodd hψ.1 hψ.2.1]
  exact hEig.2.2 ψ hψ.memRestrictedFormDomain

end Torsion.Spectral

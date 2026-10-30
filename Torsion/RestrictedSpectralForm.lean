import Torsion.SpectralDefinitions
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Positivity and algebra of the actual restricted Fourier form

The normalization here is the `exp(-i x ξ)` normalization in the source.
These results concern that concrete integral, not an abstract replacement
operator. No spectral existence theorem is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- Conversion to mathlib's Fourier convention; the frequency is divided by
`2π`, and the source's energy normalization is kept unchanged. -/
theorem fourier_eq_mathlib (f : ℝ → ℝ) (ξ : ℝ) :
    fourier f ξ = 𝓕 (fun x => (f x : ℂ)) (ξ / (2 * Real.pi)) := by
  rw [Real.fourierIntegral_real_eq_integral_exp_smul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    have hp : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    have h : -2 * Real.pi * x * (ξ / (2 * Real.pi)) = -(x * ξ) := by
      field_simp
      ring
    simp only [h, Complex.ofReal_neg, smul_eq_mul]

/-- The diagonal of the concrete bilinear integral is its nonnegative
weighted squared Fourier norm. -/
theorem energy_self (f : ℝ → ℝ) :
    energy f f = (1 / (2 * Real.pi)) * ∫ ξ : ℝ, |ξ| * ‖fourier f ξ‖ ^ 2 := by
  unfold energy
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    dsimp only
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.star_def, Complex.mul_conj]

theorem energy_nonneg (f : ℝ → ℝ) : 0 ≤ energy f f := by
  rw [energy_self]
  apply mul_nonneg (by positivity)
  exact integral_nonneg fun ξ => mul_nonneg (abs_nonneg _) (sq_nonneg _)

theorem energy_symm (f g : ℝ → ℝ) : energy f g = energy g f := by
  unfold energy
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    dsimp only
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring

/-- A compactly supported smooth function, regarded as a Schwartz function.
This construction is used to test the injectivity of the L¹ Fourier transform. -/
def compactSmoothSchwartz {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcompact : HasCompactSupport ψ) : 𝓢(ℝ, ℂ) where
  toFun x := (ψ x : ℂ)
  smooth' := Complex.ofRealCLM.contDiff.comp hψ
  decay' k n := by
    have hfc : HasCompactSupport (fun x : ℝ => (ψ x : ℂ)) :=
      hcompact.comp_left (g := Complex.ofReal) Complex.ofReal_zero
    have hdfc : HasCompactSupport
        (iteratedFDeriv ℝ n (fun x : ℝ => (ψ x : ℂ))) := hfc.iteratedFDeriv n
    have hnormc : HasCompactSupport (fun x : ℝ =>
        ‖iteratedFDeriv ℝ n (fun x : ℝ => (ψ x : ℂ)) x‖) := hdfc.norm
    have hc : HasCompactSupport (fun x : ℝ => ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (fun x : ℝ => (ψ x : ℂ)) x‖) := by
      exact hnormc.mul_left
    have hcont : Continuous (fun x : ℝ => ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (fun x : ℝ => (ψ x : ℂ)) x‖) := by
      exact (continuous_norm.pow k).mul
        ((Complex.ofRealCLM.contDiff.comp hψ).continuous_iteratedFDeriv
          (show (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from by
            exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).norm
    obtain ⟨C, hC⟩ := (hc.isCompact_range hcont).bddAbove
    exact ⟨C, fun x => hC (mem_range_self x)⟩

/-- L¹ Fourier uniqueness obtained from actual Schwartz inversion and smooth
test separation. No continuity of the original function is required. -/
theorem ae_eq_zero_of_mathlib_fourier_eq_zero {f : ℝ → ℂ}
    (hf : Integrable f) (hF : Real.fourierIntegral f = 0) :
    f =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro ψ hψ hc
  let ψS := compactSmoothSchwartz hψ hc
  let g := (SchwartzMap.fourierTransformCLE ℂ).symm ψS
  have hg (x : ℝ) : Real.fourierIntegral g x = (ψ x : ℂ) := by
    exact congrArg (fun h : 𝓢(ℝ, ℂ) => h x)
      ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply ψS)
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact real_inner_comm (x : ℝ) (y : ℝ)
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (L := innerₗ ℝ) (μ := volume) (ν := volume) (ContinuousLinearMap.mul ℂ ℂ)
    Real.continuous_fourierChar continuous_inner hf g.integrable
  rw [hflip] at h
  change (∫ ξ : ℝ, Real.fourierIntegral f ξ * g ξ) =
    ∫ x : ℝ, f x * Real.fourierIntegral g x at h
  have hz : (∫ ξ : ℝ, Real.fourierIntegral f ξ * g ξ) = 0 := by
    simp [hF]
  rw [hz] at h
  calc
    (∫ x, ψ x • f x) = ∫ x, f x * Real.fourierIntegral g x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [hg]
        simp [Complex.real_smul, mul_comm]
    _ = 0 := h.symm

/-- Uniqueness in the Fourier convention used by the source. -/
theorem ae_eq_zero_of_fourier_eq_zero {f : ℝ → ℝ}
    (hf : Integrable f) (hF : fourier f = 0) : f =ᵐ[volume] 0 := by
  have hfc : Integrable (fun x => (f x : ℂ)) := Complex.ofRealCLM.integrable_comp hf
  have hz : Real.fourierIntegral (fun x => (f x : ℂ)) = 0 := by
    ext ξ
    have h := congrFun hF (2 * Real.pi * ξ)
    rw [fourier_eq_mathlib] at h
    simpa [mul_div_cancel_left₀, Real.pi_ne_zero] using h
  filter_upwards [ae_eq_zero_of_mathlib_fourier_eq_zero hfc hz] with x hx
  exact Complex.ofReal_injective hx

theorem fourier_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) :
    fourier f = fourier g := by
  ext ξ
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  simp only [hx]

@[simp] theorem fourier_zero : fourier (fun _ => 0) = 0 := by
  ext ξ
  simp [fourier]

theorem fourier_continuous {f : ℝ → ℝ} (hf : Integrable f) :
    Continuous (fourier f) := by
  have hfc : Integrable (fun x => (f x : ℂ)) := Complex.ofRealCLM.integrable_comp hf
  have hcont : Continuous (Real.fourierIntegral (fun x => (f x : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hfc
  have heq : fourier f = fun ξ =>
      Real.fourierIntegral (fun x => (f x : ℂ)) (ξ / (2 * Real.pi)) :=
    funext (fourier_eq_mathlib f)
  rw [heq]
  exact hcont.comp (continuous_id.div_const _)

/-- The actual Fourier form has zero energy only on the zero L² class.
The proof uses Fourier uniqueness, not a postulated Poincaré inequality. -/
theorem energy_eq_zero_iff {f : ℝ → ℝ} (hf : Integrable f) (he : FiniteEnergy f) :
    energy f f = 0 ↔ f =ᵐ[volume] 0 := by
  constructor
  · intro hz
    rw [energy_self] at hz
    have hp : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by positivity
    have hi : (∫ ξ : ℝ, |ξ| * ‖fourier f ξ‖ ^ 2) = 0 :=
      (mul_eq_zero.mp hz).resolve_left hp
    have hi0 : (fun ξ : ℝ => |ξ| * ‖fourier f ξ‖ ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun ξ => mul_nonneg (abs_nonneg ξ) (sq_nonneg _)) he).mp hi
    have hne0 : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
      simpa using (Set.countable_singleton (0 : ℝ)).ae_not_mem volume
    have hae : fourier f =ᵐ[volume] 0 := by
      filter_upwards [hi0, hne0] with ξ hξ hne
      have hpow : ‖fourier f ξ‖ ^ 2 = 0 :=
        (mul_eq_zero.mp hξ).resolve_left (abs_ne_zero.mpr hne)
      exact norm_eq_zero.mp (pow_eq_zero hpow)
    exact ae_eq_zero_of_fourier_eq_zero hf
      (Measure.eq_of_ae_eq hae (fourier_continuous hf) continuous_const)
  · intro hz
    have hF : fourier f = 0 := (fourier_congr_ae hz).trans fourier_zero
    simp [energy_self, hF]

theorem energy_pos {f : ℝ → ℝ} (hf : Integrable f) (he : FiniteEnergy f)
    (hne : ¬ f =ᵐ[volume] 0) : 0 < energy f f :=
  lt_of_le_of_ne (energy_nonneg f) (Ne.symm fun hz => hne ((energy_eq_zero_iff hf he).mp hz))

/-- Restricted form members really are integrable on the line: their L²
class vanishes outside a finite-measure interval. -/
theorem MemRestrictedFormDomain.integrable {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) : Integrable f := by
  have hi : IntegrableOn f (Ioo (-1 : ℝ) 1) :=
    MemLp.integrable (by norm_num) (hf.1.restrict _)
  have hI : Integrable ((Ioo (-1 : ℝ) 1).indicator f) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hi
  apply hI.congr
  filter_upwards [hf.2.2.1] with x hx
  by_cases hmem : x ∈ Ioo (-1 : ℝ) 1
  · simp [hmem]
  · simp [hmem, hx hmem]

theorem MemRestrictedFormDomain.energy_pos {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hne : ¬ f =ᵐ[volume] 0) : 0 < energy f f :=
  Torsion.Spectral.energy_pos hf.integrable hf.2.1 hne

/-- Every nonzero weak restricted eigenfunction has a strictly positive
eigenvalue. The existence or ordering of eigenpairs is not assumed. -/
theorem IsRestrictedEigenfunction.eigenvalue_pos {a : ℝ} {φ : ℝ → ℝ}
    (hφ : IsRestrictedEigenfunction a φ) : 0 < a := by
  have he : 0 < energy φ φ := hφ.1.energy_pos hφ.2.1
  rw [hφ.2.2 φ hφ.1] at he
  have hsq : 0 ≤ ∫ x : ℝ, φ x * φ x := integral_nonneg fun x => mul_self_nonneg _
  exact pos_of_mul_pos_left he hsq

/-- Products of restricted form members have genuinely convergent L²
pairing integrals. -/
theorem MemRestrictedFormDomain.integrable_mul {f g : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hg : MemRestrictedFormDomain g) :
    Integrable (fun x => f x * g x) := hf.1.integrable_mul hg.1

theorem IsRestrictedEigenfunction.square_integral_pos {a : ℝ} {φ : ℝ → ℝ}
    (hφ : IsRestrictedEigenfunction a φ) : 0 < ∫ x : ℝ, φ x * φ x := by
  have he : 0 < energy φ φ := hφ.1.energy_pos hφ.2.1
  rw [hφ.2.2 φ hφ.1] at he
  exact pos_of_mul_pos_right he hφ.eigenvalue_pos.le

/-- The actual weak eigenvalue equals its Rayleigh quotient. -/
theorem IsRestrictedEigenfunction.rayleigh_quotient {a : ℝ} {φ : ℝ → ℝ}
    (hφ : IsRestrictedEigenfunction a φ) :
    a = energy φ φ / (∫ x : ℝ, φ x * φ x) := by
  apply (eq_div_iff hφ.square_integral_pos.ne').mpr
  exact (hφ.2.2 φ hφ.1).symm

/-- Eigenfunctions with different eigenvalues are L²-orthogonal, for the
concrete restricted realization defined in the source. -/
theorem IsRestrictedEigenfunction.orthogonal {a b : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : IsRestrictedEigenfunction a φ) (hψ : IsRestrictedEigenfunction b ψ)
    (hab : a ≠ b) : (∫ x : ℝ, φ x * ψ x) = 0 := by
  have hBA : energy φ ψ = b * ∫ x : ℝ, φ x * ψ x := by
    rw [energy_symm, hψ.2.2 φ hφ.1]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => mul_comm _ _
  have hz : (a - b) * (∫ x : ℝ, φ x * ψ x) = 0 := by
    rw [sub_mul, ← hφ.2.2 ψ hψ.1, ← hBA, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab)

end Torsion.Spectral

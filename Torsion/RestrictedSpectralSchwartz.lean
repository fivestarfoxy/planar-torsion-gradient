import Torsion.RestrictedSpectralSchwartzFourier

/-!
# Actual real Schwartz test functions for the original Fourier form

Compact smooth functions are constructed as real Schwartz maps. Every real
Schwartz test has finite original half-derivative energy and integrable
polynomial Fourier moments, with no interval-support requirement.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff SchwartzMap

namespace Torsion.Spectral

def compactSmoothRealSchwartz {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) : 𝓢(ℝ, ℝ) where
  toFun := ψ
  smooth' := hψ
  decay' k n := by
    have hdf : HasCompactSupport (iteratedFDeriv ℝ n ψ) := hc.iteratedFDeriv n
    have hsupport : HasCompactSupport (fun x : ℝ => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ψ x‖) :=
      hdf.norm.mul_left
    have hcont : Continuous (fun x : ℝ => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ψ x‖) :=
      (continuous_norm.pow k).mul
        (hψ.continuous_iteratedFDeriv
          (show (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
            exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).norm
    obtain ⟨C, hC⟩ := (hsupport.isCompact_range hcont).bddAbove
    exact ⟨C, fun x => hC (mem_range_self x)⟩

@[simp] theorem compactSmoothRealSchwartz_apply {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (x : ℝ) :
    compactSmoothRealSchwartz hψ hc x = ψ x := rfl

theorem finiteEnergy_of_schwartz (S : 𝓢(ℝ, ℝ)) : FiniteEnergy S := by
  have h1 := integrable_pow_mul_norm_fourier_of_schwartz S 1
  simp only [pow_one, Real.norm_eq_abs] at h1
  let B : ℝ := ∫ x : ℝ, ‖S x‖
  apply (h1.const_mul B).mono'
    ((continuous_abs.mul ((fourier_continuous S.integrable).norm.pow 2)).aestronglyMeasurable)
  exact ae_of_all _ fun ξ => by
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    have hbound : ‖fourier S ξ‖ ≤ B := norm_fourier_le_integral_norm S ξ
    have hmul := mul_le_mul_of_nonneg_left hbound (mul_nonneg (abs_nonneg ξ) (norm_nonneg (fourier S ξ)))
    nlinarith only [hmul]

theorem integrable_abs_mul_norm_fourier_of_schwartz (S : 𝓢(ℝ, ℝ)) :
    Integrable (fun ξ : ℝ => |ξ| * ‖fourier S ξ‖) := by
  simpa only [pow_one, Real.norm_eq_abs] using integrable_pow_mul_norm_fourier_of_schwartz S 1

theorem schwartz_uniform_bound (S : 𝓢(ℝ, ℝ)) (x : ℝ) :
    |S x| ≤ SchwartzMap.seminorm ℝ 0 0 S := by
  simpa only [Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ S x

theorem schwartz_exists_uniform_bound (S : 𝓢(ℝ, ℝ)) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |S x| ≤ M := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 S + 1, ?_, fun x => ?_⟩
  · have h := schwartz_uniform_bound S 0
    linarith [abs_nonneg (S 0)]
  · linarith [schwartz_uniform_bound S x]

theorem schwartz_deriv_exists_uniform_bound (S : 𝓢(ℝ, ℝ)) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |deriv S x| ≤ M := by
  simpa only [SchwartzMap.derivCLM_apply] using
    schwartz_exists_uniform_bound (SchwartzMap.derivCLM ℝ S)

end Torsion.Spectral

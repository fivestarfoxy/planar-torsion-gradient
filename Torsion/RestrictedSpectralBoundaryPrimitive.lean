module

public import Torsion.CauchyTracePairingLimit
public import Torsion.FourierHilbertPairing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The weak derivative of the genuine Cauchy boundary value

For a Hölder density of finite energy, its original restricted Fourier
pairing is the pairing of the actual continuous real Cauchy boundary value
with the derivative of a compact smooth test. This identity does not require
pointwise differentiability of the density or its Hilbert transform.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion.Spectral

theorem IsCore.deriv {ψ : ℝ → ℝ} (hψ : IsCore ψ) : IsCore (deriv ψ) := by
  refine ⟨(contDiff_infty_iff_deriv.mp hψ.1).2, hψ.2.1.deriv, ?_⟩
  exact (closure_minimal support_deriv_subset (isClosed_tsupport ψ)).trans hψ.2.2

private theorem dampedSignMultiplier_pairing_deriv {f ψ : ℝ → ℝ}
    (hψ : IsCore ψ) (y ξ : ℝ) :
    (dampedSignMultiplier y ξ * fourier f ξ * star (fourier (deriv ψ) ξ)).re =
      Real.exp (-y * |ξ|) * (|ξ| * (fourier f ξ * star (fourier ψ ξ)).re) := by
  rw [fourier_deriv (hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1)
    (hψ.1.differentiable (by simp))
    (hψ.deriv.1.continuous.integrable_of_hasCompactSupport hψ.deriv.2.1)]
  unfold dampedSignMultiplier
  by_cases hξ : 0 < ξ
  · rw [if_pos hξ, abs_of_pos hξ]
    simp only [map_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    have heq : (Real.exp (-y * ξ) : ℂ) * Complex.I * fourier f ξ *
        ((ξ : ℂ) * -Complex.I * star (fourier ψ ξ)) =
        (Real.exp (-y * ξ) : ℂ) * (ξ : ℂ) * (fourier f ξ * star (fourier ψ ξ)) := by
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
    have heq : (Real.exp (-y * -ξ) : ℂ) * -Complex.I * fourier f ξ *
        ((ξ : ℂ) * -Complex.I * star (fourier ψ ξ)) =
        (Real.exp (-y * -ξ) : ℂ) * (-ξ : ℂ) * (fourier f ξ * star (fourier ψ ξ)) := by
      ring_nf
      simp only [Complex.I_sq]
      ring
    simp only [Complex.star_def] at heq
    rw [heq]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    ring

theorem energy_eq_realCauchyBoundary_deriv_pairing
    {f ψ : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) (hE : FiniteEnergy f)
    (hψ : IsCore ψ) :
    energy f ψ = ∫ x : ℝ, deriv ψ x * realCauchyBoundaryRe f x := by
  have hfi : Integrable f := (hf.continuous hα).integrable_of_hasCompactSupport
    (cauchyDensity_hasCompactSupport hzero)
  have hψi : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have hdi : Integrable (deriv ψ) :=
    hψ.deriv.1.continuous.integrable_of_hasCompactSupport hψ.deriv.2.1
  have hlimE := damped_energy_tendsto hfi hψi hE hψ.memRestrictedFormDomain.2.1
  have hlimT := realCauchy_pairing_tendsto_boundary hf hα hzero hψ.deriv
  have heq : (fun y : ℝ => (1 / (2 * Real.pi)) * ∫ ξ : ℝ,
      Real.exp (-y * |ξ|) * |ξ| * (fourier f ξ * star (fourier ψ ξ)).re) =ᶠ[𝓝[>] 0]
      (fun y : ℝ => ∫ x : ℝ,
        deriv ψ x * (realCauchy f ((x : ℂ) + (y : ℂ) * Complex.I)).re) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have h := damped_hilbert_fourier_pairing hfi hdi hy
    have hr := congrArg Complex.re h
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
    have hire : (∫ ξ : ℝ, dampedSignMultiplier y ξ * fourier f ξ *
        star (fourier (deriv ψ) ξ)).re = ∫ ξ : ℝ,
        (dampedSignMultiplier y ξ * fourier f ξ * star (fourier (deriv ψ) ξ)).re :=
      (integral_re (integrable_dampedSignMultiplier_fourier_pairing hfi hdi hy)).symm
    rw [hire] at hr
    simp_rw [dampedSignMultiplier_pairing_deriv hψ] at hr
    have hreal : (∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * ∫ s : ℝ, (f s : ℂ) *
        ((-(x - s) / (Real.pi * ((x - s) ^ 2 + y ^ 2)) : ℝ) : ℂ)).re =
        ∫ x : ℝ, deriv ψ x * (realCauchy f ((x : ℂ) + (y : ℂ) * Complex.I)).re := by
      simp only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_re]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [integral_realCauchy_kernel_eq (hf.continuous hα) hzero hy x]
    rw [hreal] at hr
    simpa only [mul_assoc] using hr
  exact tendsto_nhds_unique hlimE (hlimT.congr' heq.symm)

end Torsion.Spectral

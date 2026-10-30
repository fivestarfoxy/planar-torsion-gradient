module

public import Torsion.RestrictedSpectralFourierIdentification
public import Torsion.RestrictedSpectralExteriorEnergy
public import Torsion.RestrictedSpectralExteriorKernel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Interior composition with the actual exterior residual

Once the whole-line weak equation has been identified across the two
endpoints, Schwartz test separation and the actual exterior kernel give
the classical second-order equation. The proof uses the original Fourier
energy, ordinary integration by parts, and the original residual integral.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

theorem energy_const_mul_sub_left_of_integrable_core {f r ψ : ℝ → ℝ}
    (hf : Integrable f) (hr : Integrable r) (hψ : IsCore ψ) (a : ℝ) :
    energy (fun x => a * f x - r x) ψ = a * energy f ψ - energy r ψ := by
  have hif := energy_integrand_integrable_of_integrable_core hf hψ
  have hir := energy_integrand_integrable_of_integrable_core hr hψ
  unfold energy
  have heq : (fun ξ : ℝ => |ξ| *
      (fourier (fun x => a * f x - r x) ξ * star (fourier ψ ξ)).re) =
      fun ξ => a * (|ξ| * (fourier f ξ * star (fourier ψ ξ)).re) -
        |ξ| * (fourier r ξ * star (fourier ψ ξ)).re := by
    funext ξ
    rw [fourier_sub (hf.const_mul a) hr, fourier_const_mul]
    simp only [Pi.sub_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [heq, integral_sub (hif.const_mul a) hir, integral_const_mul]
  ring

theorem integral_mul_second_deriv_eq_second_deriv_mul_of_local_contDiff
    {f ψ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ U) :
    (∫ x : ℝ, f x * deriv (deriv ψ) x) =
      ∫ x : ℝ, deriv (deriv f) x * ψ x := by
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hdf : ContDiffOn ℝ ∞ (deriv f) U := hf.deriv_of_isOpen hU (by simp)
  have hdsupp : tsupport (deriv ψ) ⊆ U :=
    (closure_minimal support_deriv_subset (isClosed_tsupport ψ)).trans hsupp
  rw [integral_mul_deriv_eq_neg_deriv_mul_of_local_contDiff hU
    (hf.of_le (by simp)) hdψ hc.deriv hdsupp,
    integral_mul_deriv_eq_neg_deriv_mul_of_local_contDiff hU
      (hdf.of_le (by simp)) hψ hc hsupp, neg_neg]

/-- The genuine global weak equation gives the classical composition
identity with the original exterior residual. Only integrability of that
actual residual and genuine local smoothness are used in this step. -/
theorem IsRestrictedEigenfunction.second_deriv_eq_of_global_schwartz_equation
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hreg : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hr : Integrable (exteriorResidualZero f))
    (hglobal : ∀ S : 𝓢(ℝ, ℝ), energy f S =
      ∫ x : ℝ, (a * f x - exteriorResidualZero f x) * S x)
    (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    deriv (deriv f) x = -a ^ 2 * f x - (1 / Real.pi) *
      ∫ y : ℝ, exteriorResidualZero f y / (x - y) ^ 2 := by
  let r : ℝ → ℝ := exteriorResidualZero f
  let q : ℝ → ℝ := fun x => a * f x - r x
  have hri : Integrable r := hr
  have hqi : Integrable q := (hf.1.integrable.const_mul a).sub hri
  have hrzero : ∀ᵐ y : ℝ, y ∈ Ioo (-1 : ℝ) 1 → r y = 0 := by
    exact ae_of_all _ fun y hy => by
      simp only [r, exteriorResidualZero, if_neg (not_lt.2 (abs_lt.2 hy).le)]
  have hF := fourier_eq_abs_mul_of_schwartz_equation hf.1.integrable hqi hglobal
  let P : ℝ → ℝ := fun t => ∫ y : ℝ, r y / (t - y) ^ 2
  have hPc : ContinuousOn P (Ioo (-1 : ℝ) 1) := fun t ht =>
    (continuousAt_integral_exterior_div_pow hri hrzero (abs_lt.2 ht) 2).continuousWithinAt
  have hdf : ContDiffOn ℝ ∞ (deriv f) (Ioo (-1 : ℝ) 1) :=
    hreg.deriv_of_isOpen isOpen_Ioo (by simp)
  have hddf : ContDiffOn ℝ ∞ (deriv (deriv f)) (Ioo (-1 : ℝ) 1) :=
    hdf.deriv_of_isOpen isOpen_Ioo (by simp)
  have hddfc : ContinuousOn (deriv (deriv f)) (Ioo (-1 : ℝ) 1) := hddf.continuousOn
  let D : ℝ → ℝ := fun t => deriv (deriv f) t + a ^ 2 * f t + (1 / Real.pi) * P t
  have hDc : ContinuousOn D (Ioo (-1 : ℝ) 1) :=
    (hddfc.add (continuousOn_const.mul hreg.continuousOn)).add (continuousOn_const.mul hPc)
  have hDae : D =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] 0 := by
    change ∀ᵐ t : ℝ ∂volume.restrict (Ioo (-1 : ℝ) 1), D t = 0
    rw [ae_restrict_iff' measurableSet_Ioo]
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hDc.locallyIntegrableOn measurableSet_Ioo)
    intro ψ hψ hc hsupp
    have hcore : IsCore ψ := ⟨hψ, hc, hsupp⟩
    have hcomp := energy_eq_neg_integral_second_deriv_of_fourier_mul_abs
      hf.1.integrable hF hψ hc
    have hlin := energy_const_mul_sub_left_of_integrable_core hf.1.integrable hri hcore a
    have hext := energy_eq_exterior_kernel_pairing hri hrzero hcore
    have hibp := integral_mul_second_deriv_eq_second_deriv_mul_of_local_contDiff
      isOpen_Ioo hreg hψ hc hsupp
    change energy q ψ = _ at hlin
    rw [hlin, hf.2.2 ψ hcore.memRestrictedFormDomain, hext, hibp] at hcomp
    have hddfi : Integrable (fun t : ℝ => deriv (deriv f) t * ψ t) :=
      (continuous_mul_of_tsupport_subset isOpen_Ioo hddfc hψ.continuous hsupp).integrable_of_hasCompactSupport hc.mul_left
    have hfi : Integrable (fun t : ℝ => f t * ψ t) :=
      (continuous_mul_of_tsupport_subset isOpen_Ioo hreg.continuousOn hψ.continuous hsupp).integrable_of_hasCompactSupport hc.mul_left
    have hPi : Integrable (fun t : ℝ => P t * ψ t) :=
      (continuous_mul_of_tsupport_subset isOpen_Ioo hPc hψ.continuous hsupp).integrable_of_hasCompactSupport hc.mul_left
    have hpoint : (fun t : ℝ => ψ t • D t) = fun t =>
        deriv (deriv f) t * ψ t + a ^ 2 * (f t * ψ t) + (1 / Real.pi) * (P t * ψ t) := by
      funext t
      dsimp only [D, smul_eq_mul]
      ring
    have hsum : Integrable (fun t : ℝ => deriv (deriv f) t * ψ t + a ^ 2 * (f t * ψ t)) :=
      hddfi.add (hfi.const_mul (a ^ 2))
    rw [hpoint, integral_add hsum (hPi.const_mul (1 / Real.pi)),
      integral_add hddfi (hfi.const_mul _), integral_const_mul, integral_const_mul]
    have hswap : (∫ t : ℝ, ψ t * (∫ y : ℝ, r y / (t - y) ^ 2)) =
        ∫ t : ℝ, P t * ψ t := by congr 1; funext t; dsimp only [P]; ring
    rw [hswap] at hcomp
    nlinarith [hcomp]
  have hDon : EqOn D (fun _ => 0) (Ioo (-1 : ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq hDae isOpen_Ioo hDc continuousOn_const
  have h := hDon hx
  dsimp only [D, P, r] at h
  linarith

end Torsion.Spectral

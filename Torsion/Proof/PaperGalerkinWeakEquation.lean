module

public import Torsion.Proof.PaperGalerkinAdmission
public import Torsion.Proof.PaperGalerkinModes
public import Torsion.RestrictedSpectralExteriorTest
public import Torsion.RestrictedSpectralPairingContinuity

@[expose] public section

/-! # The weak restricted half-Laplacian of the Galerkin modes

The real Cauchy trace gives the energy on smooth compactly supported tests.
The defining core approximation in the restricted form norm extends the
identity to every test in the original form domain. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace Torsion.Galerkin
open Spectral Polynomial.Chebyshev

theorem trialMode_memRestrictedFormDomain (k : ℕ) : MemRestrictedFormDomain (trialMode k) := by
  convert polynomial_semicircle_memRestrictedFormDomain (U ℝ ((k : ℤ) - 1)) using 1
  funext x
  exact mul_comm _ _

private theorem polynomial_integration_by_parts (p : Polynomial ℝ) (ψ : ℝ → ℝ)
    (hψ : IsCore ψ) :
    (∫ x : ℝ, -p.eval x * deriv ψ x) = ∫ x : ℝ, p.derivative.eval x * ψ x := by
  have hdψ := hψ.1.differentiable (by simp)
  have hi1 : Integrable (fun x : ℝ => -p.eval x * deriv ψ x) :=
    (p.continuous.neg.mul hψ.deriv.1.continuous).integrable_of_hasCompactSupport hψ.deriv.2.1.mul_left
  have hi2 : Integrable (fun x : ℝ => -p.derivative.eval x * ψ x) :=
    (p.derivative.continuous.neg.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
  have hi3 : Integrable (fun x : ℝ => -p.eval x * ψ x) :=
    (p.continuous.neg.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x : ℝ => fun _ => (p.hasDerivAt x).neg) (fun x => fun _ => (hdψ x).hasDerivAt)
    hi1 hi2 hi3
  simpa only [Pi.mul_apply, Pi.neg_apply, neg_mul, integral_neg, neg_neg] using! h

theorem trialMode_core_equation (k : ℕ) (hk : 0 < k) (ψ : ℝ → ℝ) (hψ : IsCore ψ) :
    energy (trialMode k) ψ =
      ∫ x in Ioo (-1 : ℝ) 1, ((k : ℝ) * (U ℝ ((k : ℤ) - 1)).eval x) * ψ x := by
  obtain ⟨C, hC⟩ := semicircle_polynomial_holder (U ℝ ((k : ℤ) - 1))
  change HolderWith C (1 / 2) (trialMode k) at hC
  rw [energy_eq_realCauchyBoundary_deriv_pairing hC (by norm_num : (0 : ℝ≥0) < 1 / 2)
    (trialMode_zero_exterior k) (trialMode_memRestrictedFormDomain k).2.1 hψ]
  have heq : (∫ x : ℝ, deriv ψ x * realCauchyBoundaryRe (trialMode k) x) =
      ∫ x : ℝ, -(T ℝ (k : ℤ)).eval x * deriv ψ x := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      by_cases hx : x ∈ Ioo (-1 : ℝ) 1
      · rw [trialMode_cauchyBoundary k hk (abs_lt.2 hx)]
        ring
      · have hz : deriv ψ x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (hψ.deriv.2.2 h))
        rw [hz]
        ring
  rw [heq, polynomial_integration_by_parts _ ψ hψ, T_derivative_eq_U]
  simp only [Polynomial.eval_mul, Int.cast_natCast, Polynomial.eval_natCast]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hψ.2.2 h))
  simp [hz]

/-- A continuous forcing on the closed interval determines a continuous functional
along the core approximants in the restricted form norm. -/
private theorem extend_core_equation {f P : ℝ → ℝ} (hf : MemRestrictedFormDomain f)
    (hP : Continuous P)
    (hcore : ∀ g, IsCore g → energy f g = ∫ x in Ioo (-1 : ℝ) 1, P x * g x)
    (ψ : ℝ → ℝ) (hψ : MemRestrictedFormDomain ψ) :
    energy f ψ = ∫ x in Ioo (-1 : ℝ) 1, P x * ψ x := by
  obtain ⟨v, hv, hL2, hE⟩ := hψ.2.2.2
  have hvI (n : ℕ) : Integrable (v n) := (hv n).memRestrictedFormDomain.integrable
  have hvE (n : ℕ) : FiniteEnergy (v n) := (hv n).memRestrictedFormDomain.2.1
  have hvzero (n : ℕ) : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0 :=
    (hv n).memRestrictedFormDomain.2.2.1
  have hL1 := tendsto_eLpNorm_one_of_two_zero_exterior
    (fun n => (hv n).memRestrictedFormDomain.1) hψ.1 hvzero hψ.2.2.1 hL2
  have hL := integral_norm_sub_tendsto_of_eLpNorm_one hvI hψ.integrable hL1
  let χ : ContDiffBump (0 : ℝ) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  have hχ (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) : χ x = 1 :=
    χ.one_of_mem_closedBall (by
      change dist x 0 ≤ 1
      simpa [Real.dist_eq] using (abs_lt.2 hx).le)
  have heq {g : ℝ → ℝ} (hg : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → g x = 0) :
      (∫ x : ℝ, g x * (χ x * P x)) = ∫ x in Ioo (-1 : ℝ) 1, P x * g x := by
    rw [← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    by_cases hi : x ∈ Ioo (-1 : ℝ) 1
    · simp [indicator_of_mem hi, hχ x hi, mul_comm]
    · simp [indicator_of_notMem hi, hx hi]
  have hR := integral_mul_tendsto_of_integral_norm_sub hψ.integrable hvI hL
    (χ.continuous.mul hP) χ.hasCompactSupport.mul_right
  have hleft := energy_pairing_tendsto_of_difference hψ.integrable hf.integrable hvI
    hψ.2.1 hf.2.1 hvE hE
  have hseq (n : ℕ) : energy (v n) f = ∫ x in Ioo (-1 : ℝ) 1, P x * v n x :=
    (energy_symm (v n) f).trans (hcore _ (hv n))
  rw [energy_symm]
  exact tendsto_nhds_unique (by simpa only [hseq] using hleft)
    (by simpa only [Pi.mul_apply, heq (hvzero _), heq hψ.2.2.1] using hR)

/-- The actual Fourier energy of the zero-exterior mode against any member of
the restricted form domain, with its polynomial interval forcing. -/
theorem trialMode_weak_equation (k : ℕ) (hk : 0 < k) (ψ : ℝ → ℝ)
    (hψ : MemRestrictedFormDomain ψ) :
    energy (trialMode k) ψ =
      ∫ x in Ioo (-1 : ℝ) 1, ((k : ℝ) * (U ℝ ((k : ℤ) - 1)).eval x) * ψ x :=
  extend_core_equation (trialMode_memRestrictedFormDomain k)
    (continuous_const.mul (U ℝ ((k : ℤ) - 1)).continuous) (trialMode_core_equation k hk) ψ hψ

end Torsion.Galerkin

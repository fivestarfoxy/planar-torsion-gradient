module

public import Torsion.RestrictedSpectralStrictMarkov
public import Torsion.RestrictedSpectralMinimizer

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Constant sign and simplicity of the genuine lowest restricted eigenvalue

The actual global Rayleigh lower bound forces equality in the proved strict
Markov contraction. Thus every weak eigenfunction at that lowest value has
a single a.e. sign and nonzero ordinary integral. A linear combination of
two such eigenfunctions with integral zero must vanish, proving simplicity
of the actual eigenspace. No first/second-eigenpair classification is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- Every actual eigenfunction at the lowest Rayleigh value has one a.e.
sign, by strict absolute-value contraction of the original Fourier form. -/
theorem IsRestrictedEigenfunction.sign_of_rayleigh_lower_bound {a : ℝ} {f : ℝ → ℝ}
    (hf : IsRestrictedEigenfunction a f)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) :
    0 ≤ᵐ[volume] f ∨ f ≤ᵐ[volume] 0 := by
  apply (energy_abs_eq_iff_sign hf.1).1
  have heq := (hf.abs_of_rayleigh_lower_bound hlower).2.2 _ hf.1.abs
  have hself := hf.2.2 f hf.1
  simp only [← pow_two, sq_abs] at heq hself
  exact heq.trans hself.symm

/-- A nonzero integrable function of one a.e. sign has nonzero integral. -/
theorem integral_ne_zero_of_ae_sign {f : ℝ → ℝ} (hf : Integrable f)
    (hne : ¬ f =ᵐ[volume] 0) (hsign : 0 ≤ᵐ[volume] f ∨ f ≤ᵐ[volume] 0) :
    (∫ x : ℝ, f x) ≠ 0 := by
  intro hz
  rcases hsign with hpos | hneg
  · exact hne ((integral_eq_zero_iff_of_nonneg_ae hpos hf).1 hz)
  · have hneg' : 0 ≤ᵐ[volume] (fun x => -f x) := by
      filter_upwards [hneg] with x hx
      change 0 ≤ -f x
      exact neg_nonneg.2 hx
    have hz' : (∫ x : ℝ, -f x) = 0 := by rw [integral_neg, hz, neg_zero]
    have hae := (integral_eq_zero_iff_of_nonneg_ae hneg' hf.neg).1 hz'
    apply hne
    filter_upwards [hae] with x hx
    change -f x = 0 at hx
    simpa using hx

/-- The actual lowest eigenfunction has nonzero ordinary mass; this is
proved from its variational property, not assumed as a normalization. -/
theorem IsRestrictedEigenfunction.integral_ne_zero_of_rayleigh_lower_bound {a : ℝ} {f : ℝ → ℝ}
    (hf : IsRestrictedEigenfunction a f)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) :
    (∫ x : ℝ, f x) ≠ 0 :=
  integral_ne_zero_of_ae_sign hf.1.integrable hf.2.1 (hf.sign_of_rayleigh_lower_bound hlower)

/-- A zero-integral actual lowest weak eigenfunction would have to vanish.
The lemma also allows the zero function, so no artificial nonzero instance
is introduced for the difference used in the simplicity proof. -/
theorem ae_eq_zero_of_ground_equation_integral_zero {a : ℝ} {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f)
    (hweak : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → energy f ψ = a * ∫ x : ℝ, f x * ψ x)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ)
    (hmass : (∫ x : ℝ, f x) = 0) : f =ᵐ[volume] 0 := by
  by_contra hne
  have heigen : IsRestrictedEigenfunction a f := ⟨hf, hne, hweak⟩
  exact (heigen.integral_ne_zero_of_rayleigh_lower_bound hlower) hmass

/-- Simplicity of the actual lowest restricted eigenspace, with the exact
proportionality coefficient given by the genuine ordinary integrals. -/
theorem IsRestrictedEigenfunction.ae_eq_integral_ratio_mul_of_rayleigh_lower_bound
    {a : ℝ} {f g : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hg : IsRestrictedEigenfunction a g)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) :
    g =ᵐ[volume] fun x => ((∫ y : ℝ, g y) / (∫ y : ℝ, f y)) * f x := by
  classical
  let mf : ℝ := ∫ x : ℝ, f x
  let mg : ℝ := ∫ x : ℝ, g x
  let h : ℝ → ℝ := fun x => mf * g x + (-mg) * f x
  have hmf : mf ≠ 0 := hf.integral_ne_zero_of_rayleigh_lower_bound hlower
  have hform : MemRestrictedFormDomain h := (hg.1.const_mul mf).add (hf.1.const_mul (-mg))
  have hmass : (∫ x : ℝ, h x) = 0 := by
    rw [show h = fun x => mf * g x + (-mg) * f x from rfl,
      integral_add (hg.1.integrable.const_mul mf) (hf.1.integrable.const_mul (-mg)),
      integral_const_mul, integral_const_mul]
    change mf * mg + (-mg) * mf = 0
    ring
  have hzero : h =ᵐ[volume] 0 := by
    by_contra hne
    have heigen : IsRestrictedEigenfunction a h := hg.linear_combination hf hne
    exact (heigen.integral_ne_zero_of_rayleigh_lower_bound hlower) hmass
  filter_upwards [hzero] with x hx
  change mf * g x + (-mg) * f x = 0 at hx
  change g x = (mg / mf) * f x
  field_simp [hmf]
  nlinarith

/-- An actual eigenfunction orthogonal to a lowest-Rayleigh eigenfunction
cannot have the same eigenvalue. This is the strict spectral-gap input
needed after constructing a second orthogonal eigenpair. -/
theorem IsRestrictedEigenfunction.eigenvalue_ne_of_orthogonal_to_ground
    {a b : ℝ} {f g : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hg : IsRestrictedEigenfunction b g)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ)
    (horth : (∫ x : ℝ, f x * g x) = 0) : b ≠ a := by
  intro hba
  subst b
  let c : ℝ := (∫ y : ℝ, g y) / (∫ y : ℝ, f y)
  have hae : g =ᵐ[volume] fun x => c * f x :=
    hf.ae_eq_integral_ratio_mul_of_rayleigh_lower_bound hg hlower
  have hint : (∫ x : ℝ, f x * g x) = c * ∫ x : ℝ, f x * f x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
    ring
  have hc : c = 0 := by
    rw [horth] at hint
    exact (mul_eq_zero.1 hint.symm).resolve_right hf.square_integral_pos.ne'
  apply hg.2.1
  filter_upwards [hae] with x hx
  simpa only [hc, zero_mul] using hx


/-- Every actual lowest restricted eigenfunction is even as an L² class.
Reflection preserves the weak equation and ordinary integral; simplicity
therefore forces the reflection coefficient to be exactly one. -/
theorem IsRestrictedEigenfunction.even_ae_of_rayleigh_lower_bound {a : ℝ} {f : ℝ → ℝ}
    (hf : IsRestrictedEigenfunction a f)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) :
    (fun x => f (-x)) =ᵐ[volume] f := by
  have h := hf.ae_eq_integral_ratio_mul_of_rayleigh_lower_bound hf.reflect hlower
  rw [integral_neg_eq_self f volume,
    div_self (hf.integral_ne_zero_of_rayleigh_lower_bound hlower)] at h
  simpa only [one_mul] using h

/-- Whenever the actual lowest eigenfunction is supplied with a continuous
representative, its proved parity holds pointwise on the whole line. -/
theorem IsRestrictedEigenfunction.even_of_rayleigh_lower_bound {a : ℝ} {f : ℝ → ℝ}
    (hf : IsRestrictedEigenfunction a f)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) (hcont : Continuous f) :
    Function.Even f := by
  have heq := Measure.eq_of_ae_eq (hf.even_ae_of_rayleigh_lower_bound hlower)
    (hcont.comp continuous_neg) hcont
  exact congrFun heq

end Torsion.Spectral

import Torsion.RestrictedSpectralMinimizer

/-!
# Odd-sector Rayleigh minimizers satisfy the full actual weak equation

The odd-sector Euler equation follows from odd quadratic perturbations.
Every original admissible test splits into admitted even and odd parts.
The actual Fourier energy and actual L² pairing vanish between opposite
parities, so the odd-sector equation is the full original weak equation.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform

namespace Torsion.Spectral

/-- The explicit odd projection of an actual function. -/
def restrictedOddPart (f : ℝ → ℝ) (x : ℝ) : ℝ := (f x - f (-x)) / 2

/-- The explicit even projection of an actual function. -/
def restrictedEvenPart (f : ℝ → ℝ) (x : ℝ) : ℝ := (f x + f (-x)) / 2

theorem restrictedOddPart_odd (f : ℝ → ℝ) : Function.Odd (restrictedOddPart f) := by
  intro x
  simp only [restrictedOddPart, neg_neg]
  ring

theorem restrictedEvenPart_even (f : ℝ → ℝ) : Function.Even (restrictedEvenPart f) := by
  intro x
  simp only [restrictedEvenPart, neg_neg, add_comm]

theorem restrictedOddPart_add_evenPart (f : ℝ → ℝ) :
    (fun x => restrictedOddPart f x + restrictedEvenPart f x) = f := by
  funext x
  dsimp only [restrictedOddPart, restrictedEvenPart]
  ring

/-- Both parity projections preserve the original defining restricted
form domain, by the proved reflection and vector-space closure. -/
theorem MemRestrictedFormDomain.restrictedOddPart {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) : MemRestrictedFormDomain (restrictedOddPart f) := by
  have heq : Torsion.Spectral.restrictedOddPart f =
      fun x => (1 / 2 : ℝ) * (f x + (-1 : ℝ) * f (-x)) := by
    funext x
    dsimp only [Torsion.Spectral.restrictedOddPart]
    ring
  rw [heq]
  exact (hf.add (hf.reflect.const_mul (-1))).const_mul (1 / 2)

theorem MemRestrictedFormDomain.restrictedEvenPart {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) : MemRestrictedFormDomain (restrictedEvenPart f) := by
  have heq : Torsion.Spectral.restrictedEvenPart f =
      fun x => (1 / 2 : ℝ) * (f x + f (-x)) := by
    funext x
    dsimp only [Torsion.Spectral.restrictedEvenPart]
    ring
  rw [heq]
  exact (hf.add hf.reflect).const_mul (1 / 2)

private theorem odd_linear_coefficient_eq_zero {b c : ℝ}
    (hc : 0 ≤ c) (hq : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * c) : b = 0 := by
  have hd : 0 < c + 1 := by linarith
  let t : ℝ := -b / (c + 1)
  have h := mul_nonneg (hq t) (sq_nonneg (c + 1))
  have heq : (2 * t * b + t ^ 2 * c) * (c + 1) ^ 2 = -b ^ 2 * (c + 2) := by
    dsimp only [t]
    field_simp [hd.ne']
    ring
  rw [heq] at h
  have hb : b ^ 2 = 0 := by
    nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg b) hc]
  exact pow_eq_zero hb

/-- The actual odd-sector minimum gives its weak equation against every
original odd admissible test. -/
theorem odd_weak_equation_of_rayleigh_minimum {a : ℝ} {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → Function.Odd ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ)
    (heq : energy f f = a * ∫ x : ℝ, f x ^ 2)
    {ψ : ℝ → ℝ} (hψ : MemRestrictedFormDomain ψ) (hψodd : Function.Odd ψ) :
    energy f ψ = a * ∫ x : ℝ, f x * ψ x := by
  let b : ℝ := energy f ψ - a * ∫ x : ℝ, f x * ψ x
  let c : ℝ := energy ψ ψ - a * ∫ x : ℝ, ψ x ^ 2
  have hc : 0 ≤ c := sub_nonneg.mpr (hlower ψ hψ hψodd)
  have hquad (t : ℝ) : 0 ≤ 2 * t * b + t ^ 2 * c := by
    have hpertodd : Function.Odd (fun x => f x + t * ψ x) := by
      intro x
      change f (-x) + t * ψ (-x) = -(f x + t * ψ x)
      rw [hodd x, hψodd x]
      ring
    have h := hlower (fun x => f x + t * ψ x) (hf.add (hψ.const_mul t)) hpertodd
    rw [energy_add_const_mul_self hf hψ t, integral_sq_add_const_mul hf hψ t, heq] at h
    dsimp only [b, c]
    nlinarith [h]
  exact sub_eq_zero.mp (odd_linear_coefficient_eq_zero hc hquad)

/-- A genuine nonzero odd-sector Rayleigh minimizer satisfies the full
original restricted weak equation, with arbitrary original form tests. -/
theorem isRestrictedEigenfunction_of_odd_rayleigh_minimum {a : ℝ} {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f)
    (hne : ¬ f =ᵐ[volume] 0)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → Function.Odd ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ)
    (heq : energy f f = a * ∫ x : ℝ, f x ^ 2) :
    IsRestrictedEigenfunction a f := by
  refine ⟨hf, hne, ?_⟩
  intro ψ hψ
  let ψo : ℝ → ℝ := restrictedOddPart ψ
  let ψe : ℝ → ℝ := restrictedEvenPart ψ
  have hψo : MemRestrictedFormDomain ψo := hψ.restrictedOddPart
  have hψe : MemRestrictedFormDomain ψe := hψ.restrictedEvenPart
  have heqo : energy f ψo = a * ∫ x : ℝ, f x * ψo x :=
    odd_weak_equation_of_rayleigh_minimum hf hodd hlower heq hψo (restrictedOddPart_odd ψ)
  have heqe : energy f ψe = 0 := by
    rw [energy_symm]
    exact energy_eq_zero_of_even_odd (restrictedEvenPart_even ψ) hodd
  have hpair : (∫ x : ℝ, f x * ψe x) = 0 := by
    calc
      _ = ∫ x : ℝ, ψe x * f x := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => mul_comm _ _
      _ = 0 := integral_mul_eq_zero_of_even_odd (restrictedEvenPart_even ψ) hodd
  have hsplit : ψ = fun x => ψo x + ψe x := (restrictedOddPart_add_evenPart ψ).symm
  rw [hsplit, energy_add_right hf.integrable hψo.integrable hψe.integrable
    hf.2.1 hψo.2.1 hψe.2.1, heqo, heqe, add_zero]
  have hprod : (fun x => f x * (ψo x + ψe x)) =
      fun x => f x * ψo x + f x * ψe x := by funext x; ring
  rw [hprod, integral_add (hf.integrable_mul hψo) (hf.integrable_mul hψe), hpair, add_zero]

end Torsion.Spectral

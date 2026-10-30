module

public import Torsion.RestrictedSpectralWeakPrimitive
public import Torsion.RestrictedSpectralCorePrimitive

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The actual integrated equation without datum regularity

From an odd actual weak restricted eigenfunction we derive that the
half-Laplacian Fourier distribution of its actual height differs from `aY`
by a constant on the interval. No Hilbert-transform equation is assumed.

The identification of this Fourier distribution with the already constructed
continuous real Cauchy trace is still required to obtain the pointwise linear
Hilbert equation used in the geometric construction.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- Integrating the genuine restricted weak eigenfunction equation produces
an actual constant Fourier distribution on `(-1,1)`. The constant is
constructed by testing against a normalized compact smooth bump. -/
theorem IsRestrictedEigenfunction.height_equation_of_odd
    {a : ℝ} {φ : ℝ → ℝ} (hEig : IsRestrictedEigenfunction a φ)
    (hodd : Function.Odd φ) :
    ∃ b : ℝ, ∀ ψ : ℝ → ℝ, IsCore ψ →
      energy (height φ) ψ =
        a * (∫ x : ℝ, height φ x * ψ x) - b * ∫ x : ℝ, ψ x := by
  obtain ⟨ρ, hρ, hρmean⟩ := exists_core_integral_one
  let b : ℝ := a * (∫ x : ℝ, height φ x * ρ x) - energy (height φ) ρ
  refine ⟨b, ?_⟩
  intro ψ hψ
  let c : ℝ := ∫ x : ℝ, ψ x
  let χ : ℝ → ℝ := fun x => ψ x + (-c) * ρ x
  have hψint : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have hρint : Integrable ρ := hρ.1.continuous.integrable_of_hasCompactSupport hρ.2.1
  have hχ : IsCore χ := by
    simpa only [one_mul] using hψ.linear_combination hρ 1 (-c)
  have hχmean : (∫ x : ℝ, χ x) = 0 := by
    dsimp only [χ]
    rw [integral_add hψint (hρint.const_mul (-c)), integral_const_mul, hρmean]
    dsimp only [c]
    ring
  obtain ⟨P, hP, hdP⟩ := hχ.exists_primitive_of_integral_eq_zero hχmean
  have hweak := hEig.height_derivative_equation_of_odd hodd hP
  rw [hdP] at hweak
  have hYint : Integrable (height φ) := hEig.1.height_integrable
  have hYE : FiniteEnergy (height φ) := hEig.1.finiteEnergy_height hodd
  have hE : energy (height φ) χ =
      energy (height φ) ψ + (-c) * energy (height φ) ρ := by
    dsimp only [χ]
    rw [energy_add_right hYint hψint (hρint.const_mul (-c)) hYE
      (finiteEnergy_of_contDiff_hasCompactSupport hψ.1 hψ.2.1)
      ((finiteEnergy_of_contDiff_hasCompactSupport hρ.1 hρ.2.1).const_mul hρint (-c)),
      energy_const_mul_right]
  have hYcont : Continuous (height φ) := hEig.1.height_continuous
  have hYψint : Integrable (fun x => height φ x * ψ x) :=
    (hYcont.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
  have hYρint : Integrable (fun x => height φ x * ρ x) :=
    (hYcont.mul hρ.1.continuous).integrable_of_hasCompactSupport hρ.2.1.mul_left
  have hI : (∫ x : ℝ, height φ x * χ x) =
      (∫ x : ℝ, height φ x * ψ x) + (-c) * ∫ x : ℝ, height φ x * ρ x := by
    calc
      _ = ∫ x : ℝ, height φ x * ψ x + (-c) * (height φ x * ρ x) := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by dsimp only [χ]; ring
      _ = _ := by rw [integral_add hYψint (hYρint.const_mul (-c)), integral_const_mul]
  rw [hE, hI] at hweak
  change energy (height φ) ψ = a * (∫ x : ℝ, height φ x * ψ x) - b * c
  dsimp only [b]
  linear_combination hweak

/-- The constant in the integrated Fourier equation is uniquely determined
by the actual profile, independently of the normalized bump used above. -/
theorem IsRestrictedEigenfunction.height_equation_unique_of_odd
    {a : ℝ} {φ : ℝ → ℝ} (hEig : IsRestrictedEigenfunction a φ)
    (hodd : Function.Odd φ) :
    ∃! b : ℝ, ∀ ψ : ℝ → ℝ, IsCore ψ →
      energy (height φ) ψ =
        a * (∫ x : ℝ, height φ x * ψ x) - b * ∫ x : ℝ, ψ x := by
  obtain ⟨b, hb⟩ := hEig.height_equation_of_odd hodd
  refine ⟨b, hb, ?_⟩
  intro c hc
  obtain ⟨ρ, hρ, hρmean⟩ := exists_core_integral_one
  have h₁ := hb ρ hρ
  have h₂ := hc ρ hρ
  rw [hρmean, mul_one] at h₁ h₂
  linarith

end Torsion.Spectral

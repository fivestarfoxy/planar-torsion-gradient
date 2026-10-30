import Torsion.RestrictedSpectralSelection
import Torsion.RestrictedSpectralOddMinimizer
import Torsion.RestrictedSpectralGroundSign
import Torsion.RestrictedSpectralEvenGap

/-!
# Excluding the even component below the actual even mean-zero gap

A nonzero even component of a higher eigenfunction can be combined with
an even ground eigenfunction to have ordinary mean zero. The original
Fourier form on this two-dimensional span has Rayleigh quotient no larger
than the higher eigenvalue. The proved even mean-zero gap excludes that
component. No parity conclusion is included in the hypotheses.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- A genuine higher eigenfunction below an even mean-zero form gap is
its actual odd projection almost everywhere. -/
theorem IsRestrictedEigenfunction.eq_oddPart_ae_of_even_mean_zero_gap
    {a₁ a₂ κ : ℝ} {u f : ℝ → ℝ}
    (hu : IsRestrictedEigenfunction a₁ u) (hueven : Function.Even u)
    (humass : (∫ x : ℝ, u x) ≠ 0)
    (hf : IsRestrictedEigenfunction a₂ f) (h₁₂ : a₁ < a₂) (h₂κ : a₂ < κ)
    (hgap : ∀ g : ℝ → ℝ, MemRestrictedFormDomain g → Function.Even g →
      (∫ x : ℝ, g x) = 0 → κ * (∫ x : ℝ, g x ^ 2) ≤ energy g g) :
    f =ᵐ[volume] restrictedOddPart f := by
  let e : ℝ → ℝ := restrictedEvenPart f
  have hezero : e =ᵐ[volume] 0 := by
    by_contra hene
    have hcomb : (fun x => (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * f (-x)) = e := by
      funext x
      dsimp only [e, restrictedEvenPart]
      ring
    have he : IsRestrictedEigenfunction a₂ e := by
      have h := hf.linear_combination (c := (1 / 2 : ℝ)) (d := (1 / 2 : ℝ)) hf.reflect
        (by rwa [hcomb])
      rwa [hcomb] at h
    have heven : Function.Even e := restrictedEvenPart_even f
    have heorth : (∫ x : ℝ, e x * u x) = 0 := he.orthogonal hu (ne_of_gt h₁₂)
    have heMassPos : 0 < ∫ x : ℝ, e x ^ 2 := by
      simpa only [← pow_two] using he.square_integral_pos
    have huMassNonneg : 0 ≤ ∫ x : ℝ, u x ^ 2 := integral_nonneg fun x => sq_nonneg _
    let c : ℝ := -(∫ x : ℝ, e x) / (∫ x : ℝ, u x)
    let g : ℝ → ℝ := fun x => e x + c * u x
    have hg : MemRestrictedFormDomain g := he.1.add (hu.1.const_mul c)
    have hgeven : Function.Even g := by
      intro x
      dsimp only [g]
      rw [heven x, hueven x]
    have hgmean : (∫ x : ℝ, g x) = 0 := by
      rw [show g = fun x => e x + c * u x from rfl,
        integral_add he.1.integrable (hu.1.integrable.const_mul c), integral_const_mul]
      dsimp only [c]
      field_simp [humass]
    have hmass : (∫ x : ℝ, g x ^ 2) =
        (∫ x : ℝ, e x ^ 2) + c ^ 2 * (∫ x : ℝ, u x ^ 2) := by
      rw [show g = fun x => e x + c * u x from rfl,
        integral_sq_add_const_mul he.1 hu.1 c, heorth, mul_zero, add_zero]
    have hmasspos : 0 < ∫ x : ℝ, g x ^ 2 := by
      rw [hmass]
      exact add_pos_of_pos_of_nonneg heMassPos (mul_nonneg (sq_nonneg c) huMassNonneg)
    have heSelf : energy e e = a₂ * (∫ x : ℝ, e x ^ 2) := by
      simpa only [← pow_two] using he.2.2 e he.1
    have huSelf : energy u u = a₁ * (∫ x : ℝ, u x ^ 2) := by
      simpa only [← pow_two] using hu.2.2 u hu.1
    have heCross : energy e u = 0 := by rw [he.2.2 u hu.1, heorth, mul_zero]
    have henergy : energy g g ≤ a₂ * (∫ x : ℝ, g x ^ 2) := by
      rw [show g = fun x => e x + c * u x from rfl,
        energy_add_const_mul_self he.1 hu.1 c, heSelf, huSelf, heCross,
        mul_zero, add_zero, integral_sq_add_const_mul he.1 hu.1 c,
        heorth, mul_zero, add_zero]
      have hle := mul_le_mul_of_nonneg_right h₁₂.le
        (mul_nonneg (sq_nonneg c) huMassNonneg)
      nlinarith only [hle]
    have hgapg := hgap g hg hgeven hgmean
    have hstrict := mul_lt_mul_of_pos_right h₂κ hmasspos
    exact (not_lt_of_ge (hgapg.trans henergy)) hstrict
  filter_upwards [hezero] with x hx
  change restrictedEvenPart f x = 0 at hx
  dsimp only [restrictedEvenPart] at hx
  change f x = (f x - f (-x)) / 2
  linarith

/-- The actual rational even-sector estimate excludes the even component
of every higher eigenfunction below `63/20`. Ground nonzero mass is derived
from the genuine lowest-Rayleigh property. -/
theorem IsRestrictedEigenfunction.eq_oddPart_ae_of_lt_even_gap
    {a₁ a₂ : ℝ} {u f : ℝ → ℝ}
    (hu : IsRestrictedEigenfunction a₁ u) (hueven : Function.Even u)
    (hground : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      a₁ * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ)
    (hf : IsRestrictedEigenfunction a₂ f) (h₁₂ : a₁ < a₂) (h₂gap : a₂ < (63 / 20 : ℝ)) :
    f =ᵐ[volume] restrictedOddPart f :=
  hu.eq_oddPart_ae_of_even_mean_zero_gap hueven
    (hu.integral_ne_zero_of_rayleigh_lower_bound hground) hf h₁₂ h₂gap
    (fun _ hg hgeven hgmean => hg.even_mean_zero_energy_ge hgeven hgmean)

/-- In particular, the selected genuine second eigenfunction has odd L²
parity once its concrete upper trial bound places it below the even gap. -/
theorem secondEigenfunctionL2_eq_oddPart_ae_of_lt_even_gap
    (hupper : secondEigenvalue < (63 / 20 : ℝ)) :
    secondEigenfunctionL2 =ᵐ[volume] restrictedOddPart secondEigenfunctionL2 :=
  firstEigenfunctionL2_isRestrictedEigenfunction.eq_oddPart_ae_of_lt_even_gap
    firstEigenfunctionL2_even firstEigenvalue_variational
    secondEigenfunctionL2_isRestrictedEigenfunction firstEigenvalue_lt_secondEigenvalue hupper

end Torsion.Spectral

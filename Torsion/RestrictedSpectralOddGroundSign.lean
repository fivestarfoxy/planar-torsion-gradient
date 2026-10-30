import Torsion.RestrictedSpectralOddStrictMarkov
import Torsion.RestrictedSpectralOddGroundState

/-!
# Half-line sign and simplicity of the actual least odd eigenvalue

The genuine odd-sector Rayleigh lower bound forces equality in the actual
folded-absolute contraction. Its strict gap then supplies one a.e. sign on
the positive half line. Odd reflection turns zero positive-half mass into
global vanishing, which proves simplicity of the actual odd eigenspace.
No identification of this odd eigenvalue with the second full eigenvalue
is asserted here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- An actual odd function vanishing a.e. on the positive half line
vanishes a.e. on the whole line, by measure-preserving reflection. -/
theorem ae_eq_zero_of_odd_ae_eq_zero_half {f : ℝ → ℝ} (hodd : Function.Odd f)
    (hhalf : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0) : f =ᵐ[volume] 0 := by
  have hp := ae_imp_of_ae_restrict hhalf
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hp
  have hf0 : f 0 = 0 := by have h := hodd 0; simp only [neg_zero] at h; linarith
  filter_upwards [hp, hn] with x hx hnx
  change f x = 0
  rcases lt_trichotomy x 0 with hneg | heq | hpos
  · have h := hnx (show -x ∈ Ioi (0 : ℝ) from neg_pos.2 hneg)
    change f (-x) = 0 at h
    rw [hodd x] at h
    linarith
  · simpa [heq] using hf0
  · exact hx hpos

/-- A nonzero integrable odd function with one positive-half a.e. sign
has nonzero actual positive-half integral. -/
theorem integral_half_ne_zero_of_odd_ae_half_sign {f : ℝ → ℝ}
    (hf : Integrable f) (hodd : Function.Odd f) (hne : ¬ f =ᵐ[volume] 0)
    (hsign : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f ∨
      f ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] 0) : (∫ x in Ioi (0 : ℝ), f x) ≠ 0 := by
  intro hz
  apply hne
  apply ae_eq_zero_of_odd_ae_eq_zero_half hodd
  rcases hsign with hpos | hneg
  · exact (integral_eq_zero_iff_of_nonneg_ae hpos hf.integrableOn).1 hz
  · have hneg' : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun x => -f x) := by
      filter_upwards [hneg] with x hx
      change 0 ≤ -f x
      exact neg_nonneg.2 hx
    have hz' : (∫ x in Ioi (0 : ℝ), -f x) = 0 := by rw [integral_neg, hz, neg_zero]
    have hae := (integral_eq_zero_iff_of_nonneg_ae hneg' hf.neg.integrableOn).1 hz'
    filter_upwards [hae] with x hx
    change -f x = 0 at hx
    change f x = 0
    linarith

/-- Every actual least-odd eigenfunction has a single positive-half a.e.
sign, by the strict folded-absolute Fourier-energy theorem. -/
theorem IsRestrictedEigenfunction.half_sign_of_odd_rayleigh_lower_bound
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → Function.Odd ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) :
    0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f ∨ f ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  apply energy_oddFoldAbs_eq_imp_sign hf.1 hodd
  have heq := (hf.oddFoldAbs_of_odd_rayleigh_lower_bound hodd hlower).2.2 _ (hf.1.oddFoldAbs hodd)
  have hself := hf.2.2 f hf.1
  simp only [← pow_two, oddFoldAbs_sq] at heq hself
  exact heq.trans hself.symm

/-- The actual least odd eigenfunction has nonzero positive-half mass. -/
theorem IsRestrictedEigenfunction.integral_half_ne_zero_of_odd_rayleigh_lower_bound
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → Function.Odd ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) : (∫ x in Ioi (0 : ℝ), f x) ≠ 0 :=
  integral_half_ne_zero_of_odd_ae_half_sign hf.1.integrable hodd hf.2.1
    (hf.half_sign_of_odd_rayleigh_lower_bound hodd hlower)

/-- A zero positive-half integral and the actual least-odd weak equation
force global a.e. vanishing, allowing the zero function in the statement. -/
theorem ae_eq_zero_of_odd_ground_equation_half_integral_zero {a : ℝ} {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f)
    (hweak : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → energy f ψ = a * ∫ x : ℝ, f x * ψ x)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → Function.Odd ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ)
    (hmass : (∫ x in Ioi (0 : ℝ), f x) = 0) : f =ᵐ[volume] 0 := by
  by_contra hne
  have heigen : IsRestrictedEigenfunction a f := ⟨hf, hne, hweak⟩
  exact (heigen.integral_half_ne_zero_of_odd_rayleigh_lower_bound hodd hlower) hmass

/-- Simplicity of the actual least-odd restricted eigenspace. The exact
proportionality coefficient is the ratio of the actual half-line masses. -/
theorem IsRestrictedEigenfunction.ae_eq_half_integral_ratio_mul_of_odd_rayleigh_lower_bound
    {a : ℝ} {f g : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hg : IsRestrictedEigenfunction a g)
    (hfodd : Function.Odd f) (hgodd : Function.Odd g)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → Function.Odd ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) :
    g =ᵐ[volume] fun x => ((∫ y in Ioi (0 : ℝ), g y) / (∫ y in Ioi (0 : ℝ), f y)) * f x := by
  let mf : ℝ := ∫ x in Ioi (0 : ℝ), f x
  let mg : ℝ := ∫ x in Ioi (0 : ℝ), g x
  let h : ℝ → ℝ := fun x => mf * g x + (-mg) * f x
  have hmf : mf ≠ 0 := hf.integral_half_ne_zero_of_odd_rayleigh_lower_bound hfodd hlower
  have hodd : Function.Odd h := by
    intro x
    dsimp only [h]
    rw [hgodd x, hfodd x]
    ring
  have hmass : (∫ x in Ioi (0 : ℝ), h x) = 0 := by
    rw [show h = fun x => mf * g x + (-mg) * f x from rfl,
      integral_add (hg.1.integrable.const_mul mf).integrableOn (hf.1.integrable.const_mul (-mg)).integrableOn,
      integral_const_mul, integral_const_mul]
    change mf * mg + (-mg) * mf = 0
    ring
  have hzero : h =ᵐ[volume] 0 := by
    by_contra hne
    have heigen : IsRestrictedEigenfunction a h := hg.linear_combination hf hne
    exact (heigen.integral_half_ne_zero_of_odd_rayleigh_lower_bound hodd hlower) hmass
  filter_upwards [hzero] with x hx
  change mf * g x + (-mg) * f x = 0 at hx
  change g x = (mg / mf) * f x
  field_simp [hmf]
  nlinarith

/-- Two orthogonal nonzero odd eigenfunctions cannot both belong to the
actual lowest odd eigenvalue. -/
theorem IsRestrictedEigenfunction.eigenvalue_ne_of_odd_orthogonal_to_odd_ground
    {a b : ℝ} {f g : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hg : IsRestrictedEigenfunction b g)
    (hfodd : Function.Odd f) (hgodd : Function.Odd g)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → Function.Odd ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ)
    (horth : (∫ x : ℝ, f x * g x) = 0) : b ≠ a := by
  intro hba
  subst b
  let c : ℝ := (∫ y in Ioi (0 : ℝ), g y) / (∫ y in Ioi (0 : ℝ), f y)
  have hae : g =ᵐ[volume] fun x => c * f x :=
    hf.ae_eq_half_integral_ratio_mul_of_odd_rayleigh_lower_bound hg hfodd hgodd hlower
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

/-- An actually constructed normalized least-odd eigenpair, with positive
half mass and a proved one-dimensional odd eigenspace. This instantiates
the variational sign and simplicity theorems at the existing concrete
compact-resolvent eigenpair; it does not label this eigenvalue as λ₂. -/
theorem exists_least_odd_simple_nonnegative_half_restricted_eigenpair :
    ∃ a : ℝ, 0 < a ∧ ∃ φ : ℝ → ℝ,
      IsRestrictedEigenfunction a φ ∧ Function.Odd φ ∧
      (∀ x : ℝ, 1 ≤ |x| → φ x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ φ x) ∧
      (∫ x : ℝ, φ x ^ 2) = 1 ∧
      (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → Function.Odd ψ →
        a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) ∧
      0 < (∫ x in Ioi (0 : ℝ), φ x) ∧
      (∀ ψ : ℝ → ℝ, IsRestrictedEigenfunction a ψ → Function.Odd ψ →
        ∃ c : ℝ, ψ =ᵐ[volume] fun x => c * φ x) := by
  obtain ⟨a, ha, φ, hφ, hodd, hzero, hpos, hnorm, hlower⟩ :=
    exists_least_odd_nonnegative_half_restricted_eigenpair
  refine ⟨a, ha, φ, hφ, hodd, hzero, hpos, hnorm, hlower, ?_, ?_⟩
  · have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] φ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hpos x hx.le
    exact lt_of_le_of_ne (integral_nonneg_of_ae hnonneg)
      (Ne.symm (hφ.integral_half_ne_zero_of_odd_rayleigh_lower_bound hodd hlower))
  · intro ψ hψ hψodd
    exact ⟨(∫ y in Ioi (0 : ℝ), ψ y) / (∫ y in Ioi (0 : ℝ), φ y),
      hφ.ae_eq_half_integral_ratio_mul_of_odd_rayleigh_lower_bound hψ hodd hψodd hlower⟩

end Torsion.Spectral

import Torsion.RestrictedSpectralLattice

/-!
# Actual Rayleigh minimizers satisfy the actual weak eigenfunction equation

A quadratic perturbation in the original restricted form domain proves the
Euler equation for a supplied global Rayleigh minimizer. The proved Markov
contraction then supplies nonnegative ground eigenfunctions, and reflection
supplies an even nonnegative normalized choice. These results do not assume
simplicity, strict positivity, or identify an ordered eigenvalue by fiat.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform

namespace Torsion.Spectral

private theorem linear_coefficient_eq_zero_of_nonneg_quadratic {b c : ℝ}
    (hc : 0 ≤ c) (hq : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * c) : b = 0 := by
  have hd : 0 < c + 1 := by linarith
  let t : ℝ := -b / (c + 1)
  have h := mul_nonneg (hq t) (sq_nonneg (c + 1))
  have heq : (2 * t * b + t ^ 2 * c) * (c + 1) ^ 2 = -b ^ 2 * (c + 2) := by
    dsimp [t]
    field_simp [hd.ne']
    ring
  rw [heq] at h
  have hb : b ^ 2 = 0 := by
    nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg b) hc]
  exact pow_eq_zero hb

/-- The exact quadratic energy expansion in the original concrete form. -/
theorem energy_add_const_mul_self {f g : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hg : MemRestrictedFormDomain g) (t : ℝ) :
    energy (fun x => f x + t * g x) (fun x => f x + t * g x) =
      energy f f + 2 * t * energy f g + t ^ 2 * energy g g := by
  have ht := hg.const_mul t
  have hs := hf.add ht
  rw [energy_add_left hf.integrable ht.integrable hs.integrable hf.2.1 ht.2.1 hs.2.1,
    energy_add_right hf.integrable hf.integrable ht.integrable hf.2.1 hf.2.1 ht.2.1,
    energy_add_right ht.integrable hf.integrable ht.integrable ht.2.1 hf.2.1 ht.2.1]
  simp only [energy_const_mul_left, energy_const_mul_right]
  rw [energy_symm g f]
  ring

/-- The corresponding actual Lebesgue L² mass expansion. -/
theorem integral_sq_add_const_mul {f g : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hg : MemRestrictedFormDomain g) (t : ℝ) :
    (∫ x : ℝ, (f x + t * g x) ^ 2) =
      (∫ x : ℝ, f x ^ 2) + 2 * t * (∫ x : ℝ, f x * g x) +
        t ^ 2 * ∫ x : ℝ, g x ^ 2 := by
  have hfg : Integrable (fun x => f x * g x) := hf.integrable_mul hg
  have hfirst : Integrable (fun x => f x ^ 2 + (2 * t) * (f x * g x)) :=
    hf.1.integrable_sq.add (hfg.const_mul (2 * t))
  calc
    _ = ∫ x : ℝ, (f x ^ 2 + (2 * t) * (f x * g x)) + t ^ 2 * (g x ^ 2) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only; ring
    _ = _ := by
      rw [integral_add hfirst (hg.1.integrable_sq.const_mul (t ^ 2)),
        integral_add hf.1.integrable_sq (hfg.const_mul (2 * t)),
        integral_const_mul, integral_const_mul]

/-- A genuine global Rayleigh minimizer satisfies the full actual restricted
weak Fourier equation against every original form-domain test. -/
theorem isRestrictedEigenfunction_of_rayleigh_minimum {a : ℝ} {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hne : ¬ f =ᵐ[volume] 0)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ)
    (heq : energy f f = a * ∫ x : ℝ, f x ^ 2) :
    IsRestrictedEigenfunction a f := by
  refine ⟨hf, hne, ?_⟩
  intro ψ hψ
  let b : ℝ := energy f ψ - a * ∫ x : ℝ, f x * ψ x
  let c : ℝ := energy ψ ψ - a * ∫ x : ℝ, ψ x ^ 2
  have hc : 0 ≤ c := sub_nonneg.mpr (hlower ψ hψ)
  have hquad (t : ℝ) : 0 ≤ 2 * t * b + t ^ 2 * c := by
    have h := hlower (fun x => f x + t * ψ x) (hf.add (hψ.const_mul t))
    rw [energy_add_const_mul_self hf hψ t, integral_sq_add_const_mul hf hψ t, heq] at h
    dsimp only [b, c]
    nlinarith [h]
  have hb : b = 0 := linear_coefficient_eq_zero_of_nonneg_quadratic hc hquad
  exact sub_eq_zero.mp hb

/-- Nonzero scalar rescaling preserves the actual weak eigenfunction
problem, including its nonzero L² equivalence class. -/
theorem IsRestrictedEigenfunction.const_mul {a c : ℝ} {f : ℝ → ℝ}
    (hf : IsRestrictedEigenfunction a f) (hc : c ≠ 0) :
    IsRestrictedEigenfunction a (fun x => c * f x) := by
  have hne : ¬ (fun x => c * f x) =ᵐ[volume] 0 := by
    intro h
    apply hf.2.1
    filter_upwards [h] with x hx
    exact (mul_eq_zero.mp hx).resolve_left hc
  simpa only [zero_mul, add_zero] using
    hf.linear_combination (c := c) (d := 0) hf (by simpa only [zero_mul, add_zero] using hne)

/-- The absolute value of an actual lowest-Rayleigh eigenfunction is an
actual weak eigenfunction at the same eigenvalue. Markov contraction and
the global lower bound force equality of its energies. -/
theorem IsRestrictedEigenfunction.abs_of_rayleigh_lower_bound {a : ℝ} {f : ℝ → ℝ}
    (hf : IsRestrictedEigenfunction a f)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) :
    IsRestrictedEigenfunction a (fun x => |f x|) := by
  have hne : ¬ (fun x => |f x|) =ᵐ[volume] 0 := by
    intro hz
    apply hf.2.1
    filter_upwards [hz] with x hx
    exact abs_eq_zero.mp hx
  apply isRestrictedEigenfunction_of_rayleigh_minimum hf.1.abs hne hlower
  apply le_antisymm
  · calc
      _ ≤ energy f f := energy_abs_le hf.1
      _ = a * ∫ x : ℝ, f x ^ 2 := by
        simpa only [pow_two] using hf.2.2 f hf.1
      _ = _ := by simp only [sq_abs]
  · exact hlower _ hf.1.abs

/-- The absolute-value ground choice preserves the actual L² mass. -/
theorem integral_sq_abs (f : ℝ → ℝ) :
    (∫ x : ℝ, |f x| ^ 2) = ∫ x : ℝ, f x ^ 2 := by simp only [sq_abs]

/-- From any supplied lowest-Rayleigh weak eigenfunction one constructs an
even, pointwise nonnegative, L²-normalized actual weak eigenfunction. This
does not assume simplicity or assert strict interior positivity. -/
theorem IsRestrictedEigenfunction.exists_even_nonnegative_normalized
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) :
    ∃ ψ : ℝ → ℝ, IsRestrictedEigenfunction a ψ ∧ Function.Even ψ ∧
      (∀ x : ℝ, 0 ≤ ψ x) ∧ (∫ x : ℝ, ψ x ^ 2) = 1 := by
  have hA := hf.abs_of_rayleigh_lower_bound hlower
  let g : ℝ → ℝ := fun x => |f x| + |f (-x)|
  have hgne : ¬ g =ᵐ[volume] 0 := by
    intro hz
    apply hf.2.1
    filter_upwards [hz] with x hx
    have hzero : |f x| = 0 := by
      change |f x| + |f (-x)| = 0 at hx
      linarith [abs_nonneg (f x), abs_nonneg (f (-x))]
    exact abs_eq_zero.mp hzero
  have hg : IsRestrictedEigenfunction a g := by
    simpa only [one_mul] using hA.linear_combination (c := 1) (d := 1) hA.reflect
      (by simpa only [one_mul] using hgne)
  have hgeven : Function.Even g := by
    intro x
    dsimp only [g]
    simp only [neg_neg, add_comm]
  have hgpos (x : ℝ) : 0 ≤ g x := add_nonneg (abs_nonneg _) (abs_nonneg _)
  let S : ℝ := ∫ x : ℝ, g x ^ 2
  have hS : 0 < S := by
    simpa only [S, pow_two] using hg.square_integral_pos
  let t : ℝ := (Real.sqrt S)⁻¹
  have ht : 0 < t := inv_pos.mpr (Real.sqrt_pos.mpr hS)
  refine ⟨fun x => t * g x, hg.const_mul ht.ne', ?_, ?_, ?_⟩
  · intro x
    dsimp only
    rw [hgeven x]
  · intro x
    exact mul_nonneg ht.le (hgpos x)
  · calc
      _ = t ^ 2 * S := by
        have heq : (fun x => (t * g x) ^ 2) = fun x => t ^ 2 * (g x ^ 2) := by
          funext x
          ring
        rw [heq, integral_const_mul]
      _ = 1 := by
        dsimp only [t]
        rw [inv_pow, Real.sq_sqrt hS.le]
        exact inv_mul_cancel₀ hS.ne'

end Torsion.Spectral

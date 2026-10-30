import Torsion.RestrictedSpectralLattice
import Torsion.RestrictedSpectralResolvent

/-!
# Order positivity of the actual restricted Fourier resolvent

The proved absolute-value Markov inequality implies a nonpositive pairing
between the positive and negative parts. Actual negative-part testing then
proves that the concrete Lax--Milgram resolvent preserves nonnegativity.
This is pointwise almost-everywhere positivity, not merely positivity of
its quadratic Hilbert form.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- The actual Fourier form pairs the disjoint positive and negative
parts nonpositively, as a consequence of its proved Markov property. -/
theorem energy_pos_part_neg_part_nonpos {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) :
    energy (fun x => max (f x) 0) (fun x => max (-f x) 0) ≤ 0 := by
  let p : ℝ → ℝ := fun x => max (f x) 0
  let n : ℝ → ℝ := fun x => max (-f x) 0
  have hp : MemRestrictedFormDomain p := hf.pos_part
  have hn : MemRestrictedFormDomain n := hf.neg_part
  have hneg := hn.const_mul (-1)
  have hsplit : f = fun x => p x + (-1 : ℝ) * n x := by
    funext x
    dsimp only [p, n]
    rcases le_total 0 (f x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.2 hx)]
      ring
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.2 hx)]
      ring
  have henergy : energy f f = energy p p + energy n n - 2 * energy p n := by
    calc
      energy f f = energy (fun x => p x + (-1 : ℝ) * n x)
          (fun x => p x + (-1 : ℝ) * n x) := congrArg (fun q => energy q q) hsplit
      _ = _ := by
        rw [energy_add_left hp.integrable hneg.integrable (hp.add hneg).integrable
          hp.2.1 hneg.2.1 (hp.add hneg).2.1,
          energy_add_right hp.integrable hp.integrable hneg.integrable hp.2.1 hp.2.1 hneg.2.1,
          energy_add_right hneg.integrable hp.integrable hneg.integrable hneg.2.1 hp.2.1 hneg.2.1,
          energy_const_mul_self, energy_const_mul_right, energy_const_mul_left, energy_symm n p]
        ring
  have hmarkov : energy p p + energy n n ≤ energy f f := energy_pos_part_add_neg_part_le hf
  linarith

/-- Testing against the negative part has the expected nonpositive energy
sign for the actual nonlocal Fourier form. -/
theorem energy_neg_part_le_neg_energy {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) :
    energy f (fun x => max (-f x) 0) ≤
      -energy (fun x => max (-f x) 0) (fun x => max (-f x) 0) := by
  let p : ℝ → ℝ := fun x => max (f x) 0
  let n : ℝ → ℝ := fun x => max (-f x) 0
  have hp : MemRestrictedFormDomain p := hf.pos_part
  have hn : MemRestrictedFormDomain n := hf.neg_part
  have hneg := hn.const_mul (-1)
  have hsplit : f = fun x => p x + (-1 : ℝ) * n x := by
    funext x
    dsimp only [p, n]
    rcases le_total 0 (f x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.2 hx)]
      ring
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.2 hx)]
      ring
  calc
    _ = energy (fun x => p x + (-1 : ℝ) * n x) n := congrArg (fun q => energy q n) hsplit
    _ = energy p n - energy n n := by
      rw [energy_add_left hp.integrable hneg.integrable hn.integrable hp.2.1 hneg.2.1 hn.2.1,
        energy_const_mul_left]
      ring
    _ ≤ -energy n n := by linarith [energy_pos_part_neg_part_nonpos hf]

/-- Nonnegative forcing gives a nonnegative solution of the genuine
restricted weak Fourier equation, by the admitted actual negative part. -/
theorem nonneg_of_restricted_weak_equation {F u : ℝ → ℝ}
    (hu : MemRestrictedFormDomain u) (hF : 0 ≤ᵐ[volume] F)
    (hweak : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → energy u ψ = ∫ x : ℝ, F x * ψ x) :
    0 ≤ᵐ[volume] u := by
  have hn := hu.neg_part
  have htest := hweak (fun x => max (-u x) 0) hn
  have hsource : 0 ≤ ∫ x : ℝ, F x * max (-u x) 0 := by
    apply integral_nonneg_of_ae
    filter_upwards [hF] with x hx
    exact mul_nonneg hx (le_max_right _ _)
  have hbound := energy_neg_part_le_neg_energy hu
  have hzero : energy (fun x => max (-u x) 0) (fun x => max (-u x) 0) = 0 := by
    linarith [energy_nonneg (fun x => max (-u x) 0)]
  have hae := (energy_eq_zero_iff hn.integrable hn.2.1).1 hzero
  filter_upwards [hae] with x hx
  change max (-u x) 0 = 0 at hx
  have hle := le_max_left (-u x) 0
  rw [hx] at hle
  change 0 ≤ u x
  linarith

namespace RestrictedHilbert

/-- The actual L² resolvent preserves almost-everywhere nonnegativity.
Its underlying weak solution is the already constructed complete-graph
Lax--Milgram solution. -/
theorem resolvent_preserves_nonneg {f : ValueL2} (hf : 0 ≤ᵐ[volume] (f : ℝ → ℝ)) :
    0 ≤ᵐ[volume] (resolvent f : ℝ → ℝ) := by
  apply nonneg_of_restricted_weak_equation
    (memRestrictedFormDomain_coordinates (solutionOperator f)) hf
  intro ψ hψ
  exact solutionOperator_equation f hψ


/-- The actual restricted resolvent respects the almost-everywhere order
on its original real L² source space. -/
theorem resolvent_mono_ae {f g : ValueL2}
    (hfg : (f : ℝ → ℝ) ≤ᵐ[volume] (g : ℝ → ℝ)) :
    (resolvent f : ℝ → ℝ) ≤ᵐ[volume] (resolvent g : ℝ → ℝ) := by
  have hsource : 0 ≤ᵐ[volume] ((g - f : ValueL2) : ℝ → ℝ) := by
    filter_upwards [Lp.coeFn_sub g f, hfg] with x hx hfgx
    change 0 ≤ (g - f : ValueL2) x
    rw [hx]
    exact sub_nonneg.2 hfgx
  have hsolution := resolvent_preserves_nonneg hsource
  rw [map_sub] at hsolution
  filter_upwards [hsolution, Lp.coeFn_sub (resolvent g) (resolvent f)] with x hx hsub
  change 0 ≤ (resolvent g - resolvent f : ValueL2) x at hx
  rw [hsub] at hx
  exact sub_nonneg.1 hx

end RestrictedHilbert
end Torsion.Spectral

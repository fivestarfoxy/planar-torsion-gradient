module

public import Torsion.RestrictedSpectralLatticeApprox
public import Torsion.RestrictedSpectralWeakClosure

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual absolute-value Markov contraction for the restricted Fourier form

The smooth core contraction comes from the proved real-space Gagliardo
representation. Actual core approximants to the absolute value have no
larger asymptotic energy. Closed-graph weak compactness then proves their
limit belongs to the original restricted form domain and preserves the
energy bound. No lattice property is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- Absolute value belongs to the original concrete restricted form domain
and contracts its original Fourier energy. -/
theorem MemRestrictedFormDomain.abs_energy_le {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) :
    MemRestrictedFormDomain (fun x => |f x|) ∧
      energy (fun x => |f x|) (fun x => |f x|) ≤ energy f f := by
  obtain ⟨v, w, hv, hw, hL, hbound, hE⟩ := hf.exists_abs_core_approximation
  have hmem : MemLp (fun x => |f x|) 2 volume := by
    simpa only [Real.norm_eq_abs] using hf.1.norm
  exact memRestrictedFormDomain_of_core_energy_upper_tendsto hmem hw hL
    (Eventually.of_forall hbound) hE

/-- Actual lattice admission of the absolute value, without a new closure
or Fourier multiplier assumption. -/
theorem MemRestrictedFormDomain.abs {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) :
    MemRestrictedFormDomain (fun x => |f x|) := hf.abs_energy_le.1

/-- The original Fourier form has the genuine absolute-value contraction. -/
theorem energy_abs_le {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) :
    energy (fun x => |f x|) (fun x => |f x|) ≤ energy f f := hf.abs_energy_le.2

/-- Negation preserves the original restricted form domain. -/
theorem MemRestrictedFormDomain.neg {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) :
    MemRestrictedFormDomain (fun x => -f x) := by
  simpa only [neg_one_mul] using hf.const_mul (-1)

/-- Subtraction preserves the original restricted form domain. -/
theorem MemRestrictedFormDomain.sub {f g : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hg : MemRestrictedFormDomain g) :
    MemRestrictedFormDomain (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

private theorem positive_part_eq_half (t : ℝ) : max t 0 = (1 / 2 : ℝ) * (t + |t|) := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, abs_of_nonneg ht]
    ring
  · rw [max_eq_right ht, abs_of_nonpos ht]
    ring

/-- Positive-part admission follows from the actual absolute-value theorem
and the already constructed linear restricted form closure. -/
theorem MemRestrictedFormDomain.pos_part {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) :
    MemRestrictedFormDomain (fun x => max (f x) 0) := by
  have h := (hf.add hf.abs).const_mul (1 / 2 : ℝ)
  simpa only [← positive_part_eq_half] using h

/-- Negative-part admission in the original form domain. -/
theorem MemRestrictedFormDomain.neg_part {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) :
    MemRestrictedFormDomain (fun x => max (-f x) 0) := hf.neg.pos_part

/-- Positive and negative part energies split as half of the original
and absolute-value energies, over the actual concrete Fourier integral. -/
theorem energy_pos_part_add_neg_part {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) :
    energy (fun x => max (f x) 0) (fun x => max (f x) 0) +
      energy (fun x => max (-f x) 0) (fun x => max (-f x) 0) =
        (energy f f + energy (fun x => |f x|) (fun x => |f x|)) / 2 := by
  let A : ℝ → ℝ := fun x => |f x|
  have hA : MemRestrictedFormDomain A := hf.abs
  have hp : (fun x => max (f x) 0) = fun x => (1 / 2 : ℝ) * (f x + A x) := by
    funext x
    exact positive_part_eq_half (f x)
  have hn : (fun x => max (-f x) 0) = fun x => (1 / 2 : ℝ) * ((-1 : ℝ) * f x + A x) := by
    funext x
    simpa [A] using positive_part_eq_half (-f x)
  rw [hp, hn, energy_const_mul_self, energy_const_mul_self]
  rw [energy_add_left hf.integrable hA.integrable (hf.add hA).integrable hf.2.1 hA.2.1 (hf.add hA).2.1]
  rw [energy_add_right hf.integrable hf.integrable hA.integrable hf.2.1 hf.2.1 hA.2.1,
    energy_add_right hA.integrable hf.integrable hA.integrable hA.2.1 hf.2.1 hA.2.1]
  have hneg := hf.const_mul (-1)
  rw [energy_add_left hneg.integrable hA.integrable (hneg.add hA).integrable hneg.2.1 hA.2.1 (hneg.add hA).2.1,
    energy_add_right hneg.integrable hneg.integrable hA.integrable hneg.2.1 hneg.2.1 hA.2.1,
    energy_add_right hA.integrable hneg.integrable hA.integrable hA.2.1 hneg.2.1 hA.2.1,
    energy_const_mul_self, energy_const_mul_left, energy_const_mul_right]
  ring

/-- The actual restricted form obeys the genuine positive/negative-part
Markov inequality, not merely membership of those lattice operations. -/
theorem energy_pos_part_add_neg_part_le {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) :
    energy (fun x => max (f x) 0) (fun x => max (f x) 0) +
      energy (fun x => max (-f x) 0) (fun x => max (-f x) 0) ≤ energy f f := by
  rw [energy_pos_part_add_neg_part hf]
  linarith [energy_abs_le hf]

/-- Positive part contracts the actual Fourier energy. -/
theorem energy_pos_part_le {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) :
    energy (fun x => max (f x) 0) (fun x => max (f x) 0) ≤ energy f f := by
  have h := energy_pos_part_add_neg_part_le hf
  linarith [energy_nonneg (fun x => max (-f x) 0)]

/-- The original restricted form domain is closed under maximum. -/
theorem MemRestrictedFormDomain.max {f g : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hg : MemRestrictedFormDomain g) :
    MemRestrictedFormDomain (fun x => max (f x) (g x)) := by
  have h := hg.add (hf.sub hg).pos_part
  have heq : (fun x => g x + Max.max (f x - g x) 0) = fun x => Max.max (f x) (g x) := by
    funext x
    rcases le_total (f x) (g x) with hfg | hgf
    · rw [max_eq_right hfg, max_eq_right (sub_nonpos.2 hfg), add_zero]
    · rw [max_eq_left hgf, max_eq_left (sub_nonneg.2 hgf)]
      ring
  rwa [heq] at h

/-- The original restricted form domain is closed under minimum. -/
theorem MemRestrictedFormDomain.min {f g : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hg : MemRestrictedFormDomain g) :
    MemRestrictedFormDomain (fun x => min (f x) (g x)) := by
  have h := (hf.neg.max hg.neg).neg
  simpa only [max_neg_neg, neg_neg] using h

end Torsion.Spectral

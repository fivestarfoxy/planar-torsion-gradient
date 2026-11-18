module

public import Torsion.RestrictedSpectralOddSelection

@[expose] public section

/-! # The restricted Fourier energy on a finite trial space -/

noncomputable section
open MeasureTheory

namespace Torsion.Galerkin
open Spectral

variable {ι : Type*} [DecidableEq ι]

def trialCombination (s : Finset ι) (c : ι → ℝ) (f : ι → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ s, c i * f i x

omit [DecidableEq ι] in
private theorem combination_empty (c : ι → ℝ) (f : ι → ℝ → ℝ) :
    trialCombination ∅ c f = (fun _ => 0) := by funext x; simp [trialCombination]

private theorem combination_insert {i : ι} {s : Finset ι} (hi : i ∉ s)
    (c : ι → ℝ) (f : ι → ℝ → ℝ) : trialCombination (insert i s) c f =
      fun x => c i * f i x + trialCombination s c f x := by
  funext x
  simp [trialCombination, hi]

theorem trialCombination_mem (s : Finset ι) (c : ι → ℝ) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, MemRestrictedFormDomain (f i)) :
    MemRestrictedFormDomain (trialCombination s c f) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [combination_empty]
    simpa using leastOddEigenfunctionL2_isRestrictedEigenfunction.1.const_mul 0
  | @insert i s hi ih =>
    rw [combination_insert hi]
    exact
      ((hf i (Finset.mem_insert_self ..)).const_mul (c i)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem energy_pair_trial (s : Finset ι) (c : ι → ℝ) (f : ι → ℝ → ℝ)
    {g : ℝ → ℝ} (hg : MemRestrictedFormDomain g)
    (hf : ∀ i ∈ s, MemRestrictedFormDomain (f i)) :
    energy g (trialCombination s c f) = ∑ i ∈ s, c i * energy g (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [combination_empty]
    simpa using energy_const_mul_right g g 0
  | @insert i s hi ih =>
    have hi' := ((hf i (Finset.mem_insert_self ..)).const_mul (c i))
    have hs (j) (hj : j ∈ s) := hf j (Finset.mem_insert_of_mem hj)
    have hS := trialCombination_mem s c f hs
    rw [combination_insert hi, Finset.sum_insert hi]
    rw [energy_add_right hg.integrable hi'.integrable hS.integrable hg.2.1 hi'.2.1 hS.2.1,
      energy_const_mul_right, ih hs]

omit [DecidableEq ι] in
private theorem mass_pair_trial (s : Finset ι) (c : ι → ℝ) (f : ι → ℝ → ℝ)
    {g : ℝ → ℝ} (hg : MemRestrictedFormDomain g)
    (hf : ∀ i ∈ s, MemRestrictedFormDomain (f i)) :
    (∫ x : ℝ, g x * trialCombination s c f x) =
      ∑ i ∈ s, c i * ∫ x : ℝ, g x * f i x := by
  have hp (x : ℝ) : g x * trialCombination s c f x = ∑ i ∈ s, c i * (g x * f i x) := by
    simp only [trialCombination, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hp]
  rw [integral_finsetSum _ (fun i hi => (hg.integrable_mul (hf i hi)).const_mul (c i))]
  simp only [integral_const_mul]

theorem trialCombination_energy (s : Finset ι) (c : ι → ℝ) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, MemRestrictedFormDomain (f i)) :
    energy (trialCombination s c f) (trialCombination s c f) =
      ∑ i ∈ s, c i * ∑ j ∈ s, c j * energy (f i) (f j) := by
  rw [energy_pair_trial s c f (trialCombination_mem s c f hf) hf]
  apply Finset.sum_congr rfl
  intro i hi
  rw [energy_symm, energy_pair_trial s c f (hf i hi) hf]

theorem trialCombination_mass (s : Finset ι) (c : ι → ℝ) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, MemRestrictedFormDomain (f i)) :
    (∫ x : ℝ, trialCombination s c f x ^ 2) =
      ∑ i ∈ s, c i * ∑ j ∈ s, c j * ∫ x : ℝ, f i x * f j x := by
  simp only [pow_two]
  rw [mass_pair_trial s c f (trialCombination_mem s c f hf) hf]
  apply Finset.sum_congr rfl
  intro i hi
  conv_lhs => arg 2; enter [2, x]; rw [mul_comm]
  rw [mass_pair_trial s c f (hf i hi) hf]

end Torsion.Galerkin

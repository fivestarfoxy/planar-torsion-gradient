module

public import Torsion.Proof.PaperGalerkinAdmission
public import Torsion.Proof.PaperGalerkinEnergy
public import Torsion.Proof.PaperRitzForms
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

/-! # The finite odd-sector generalized eigenvalue problem -/

noncomputable section
open Real Set MeasureTheory
open scoped Matrix
namespace Torsion.Galerkin
open Spectral

/-- The first `K` frequencies of the odd symmetry class are `2,4,...,2K`. -/
def oddSectorFrequency {K : ℕ} (i : Fin K) : ℕ := 2 * (i.val + 1)

private theorem frequency_pos {K : ℕ} (i : Fin K) : 0 < oddSectorFrequency i := by
  unfold oddSectorFrequency
  omega

private theorem frequency_injective {K : ℕ} : Function.Injective (@oddSectorFrequency K) := by
  intro i j h
  apply Fin.ext
  unfold oddSectorFrequency at h
  omega

def ritzStiffness (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.diagonal (fun i => (oddSectorFrequency i : ℝ) * π / 2)

def ritzMass (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  fun i j => 1 / (1 - ((oddSectorFrequency i : ℝ) - oddSectorFrequency j) ^ 2) -
    1 / (1 - ((oddSectorFrequency i : ℝ) + oddSectorFrequency j) ^ 2)

private theorem mode_mem (k : ℕ) : MemRestrictedFormDomain (trialMode k) := by
  have heq : trialMode k =
      fun x => (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval x * semicircleBarrier x := by
    funext x
    exact mul_comm _ _
  rw [heq]
  exact polynomial_semicircle_memRestrictedFormDomain _

theorem oddSector_trialMode_odd {K : ℕ} (i : Fin K) : Function.Odd (trialMode (oddSectorFrequency i)) := by
  intro x
  by_cases hx : |x| ≤ 1
  · rw [trialMode_sine _ (by simpa using hx), trialMode_sine _ hx, Real.arccos_neg, mul_sub]
    rw [show (oddSectorFrequency i : ℝ) * π = (i.val + 1 : ℕ) * (2 * π) by
      simp [oddSectorFrequency]; ring]
    exact Real.sin_nat_mul_two_pi_sub _ _
  · have h := le_of_not_ge hx
    simp [trialMode_zero_exterior _ _ h, trialMode_zero_exterior _ (-x) (by simpa using h)]

theorem ritzMass_entry_eq_integral {K : ℕ} (i j : Fin K) :
    ritzMass K i j = ∫ x : ℝ, trialMode (oddSectorFrequency i) x * trialMode (oddSectorFrequency j) x := by
  let k := oddSectorFrequency i
  let l := oddSectorFrequency j
  have hpar : Even ((k : ℤ) - (l : ℤ)) := by
    refine ⟨((i.val : ℤ) - (j.val : ℤ)), ?_⟩
    dsimp [k,l,oddSectorFrequency]
    ring
  have hsu : Function.support (fun x => trialMode k x * trialMode l x) ⊆ Ioc (-1 : ℝ) 1 := by
    intro x hx
    by_contra h
    have hax : 1 ≤ |x| := by
      by_contra ha
      exact h ⟨(abs_lt.mp (lt_of_not_ge ha)).1, (abs_lt.mp (lt_of_not_ge ha)).2.le⟩
    exact hx (by simp [trialMode_zero_exterior k x hax])
  rw [← intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) hsu]
  have hs : (∫ x in (-1 : ℝ)..1, trialMode k x * trialMode l x) =
      ∫ x in (-1 : ℝ)..1, sin ((k : ℝ) * arccos x) * sin ((l : ℝ) * arccos x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    simp only [trialMode_sine _ (abs_le.mpr hx)]
  rw [hs]
  simpa only [ritzMass, k, l, Int.cast_natCast] using (physicalMass k l hpar).symm

/-- The finite odd trial function associated to the coefficient vector. -/
def ritzTrial {K : ℕ} (c : Fin K → ℝ) :=
  trialCombination Finset.univ c (fun i => trialMode (oddSectorFrequency i))

theorem ritzTrial_mem {K : ℕ} (c : Fin K → ℝ) : MemRestrictedFormDomain (ritzTrial c) :=
  trialCombination_mem _ _ _ (fun _ _ => mode_mem _)

theorem ritzTrial_odd {K : ℕ} (c : Fin K → ℝ) : Function.Odd (ritzTrial c) := by
  intro x
  simp only [ritzTrial, trialCombination, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [oddSector_trialMode_odd i x, mul_neg]

theorem ritzTrial_mass {K : ℕ} (c : Fin K → ℝ) :
    (∫ x : ℝ, ritzTrial c x ^ 2) = c ⬝ᵥ (ritzMass K *ᵥ c) := by
  unfold ritzTrial
  rw [trialCombination_mass _ _ _ (fun i _ => mode_mem _)]
  unfold dotProduct Matrix.mulVec
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change _ = ritzMass K i j * c j
  rw [ritzMass_entry_eq_integral, mul_comm]

theorem ritzTrial_energy {K : ℕ} (c : Fin K → ℝ) :
    energy (ritzTrial c) (ritzTrial c) = c ⬝ᵥ (ritzStiffness K *ᵥ c) := by
  unfold ritzTrial
  rw [trialCombination_energy _ _ _ (fun i _ => mode_mem _)]
  unfold dotProduct Matrix.mulVec
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [trialMode_energy _ _ (frequency_pos i) (frequency_pos j), mul_comm]
  simp only [frequency_injective.eq_iff, ritzStiffness, Matrix.diagonal_apply]

/-- The exact odd-sector variational bound for every vector in the finite trial space. -/
theorem ritz_rayleigh (K : ℕ) (c : Fin K → ℝ) :
    secondEigenvalue * (c ⬝ᵥ (ritzMass K *ᵥ c)) ≤ c ⬝ᵥ (ritzStiffness K *ᵥ c) := by
  rw [← ritzTrial_mass, ← ritzTrial_energy]
  exact (mul_le_mul_of_nonneg_right secondEigenvalue_le_leastOddEigenvalue
    (integral_nonneg fun _ => sq_nonneg _)).trans
    (leastOddEigenvalue_variational _ (ritzTrial_mem c) (ritzTrial_odd c))

theorem ritzStiffness_posDef (K : ℕ) : (ritzStiffness K).PosDef :=
  Matrix.PosDef.diagonal fun i => div_pos (mul_pos (by exact_mod_cast frequency_pos i) pi_pos)
    (by norm_num)

/-- The physical mass matrix is positive definite, including for arbitrary truncation sizes. -/
theorem ritzMass_posDef (K : ℕ) : (ritzMass K).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, ritzMass_entry_eq_integral]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  · intro c hc
    simp only [star_trivial]
    rw [← ritzTrial_mass]
    apply lt_of_le_of_ne (integral_nonneg fun _ => sq_nonneg _)
    intro hzero
    have hF := ritzTrial_mem c
    have hsq := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (ritzTrial c x))
      hF.1.integrable_sq).mp hzero.symm
    have hae : ritzTrial c =ᵐ[volume] 0 := by
      filter_upwards [hsq] with x hx
      exact eq_zero_of_pow_eq_zero hx
    have hz := (energy_eq_zero_iff hF.integrable hF.2.1).2 hae
    rw [ritzTrial_energy] at hz
    have hp := (ritzStiffness_posDef K).dotProduct_mulVec_pos hc
    simp [hz] at hp

/-- Every generalized eigenvalue of the explicit Galerkin pencil is an upper bound
for the exact second eigenvalue of the restricted half-Laplacian. -/
theorem secondEigenvalue_le_ritz
    {K : ℕ} {μ : ℝ} {c : Fin K → ℝ} (hc : c ≠ 0)
    (heq : ritzStiffness K *ᵥ c = μ • (ritzMass K *ᵥ c)) : secondEigenvalue ≤ μ := by
  have h := ritz_rayleigh K c
  rw [heq, dotProduct_smul, smul_eq_mul] at h
  have hpos := (ritzMass_posDef K).dotProduct_mulVec_pos hc
  exact le_of_mul_le_mul_right h (by simpa using hpos)

end Torsion.Galerkin

module

public import Torsion.Proof.PaperGalerkinRitz
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

@[expose] public section

/-! # Existence of the least Galerkin generalized eigenvalue -/

noncomputable section
open Real Set Matrix WithLp MeasureTheory
open scoped Matrix
namespace Torsion.Galerkin

/-- All generalized eigenvalues of the `K`-mode stiffness and mass matrices. -/
def ritzEigenvalues (K : ℕ) : Set ℝ :=
  {μ | ∃ c : Fin K → ℝ, c ≠ 0 ∧ ritzStiffness K *ᵥ c = μ • (ritzMass K *ᵥ c)}

theorem ritzEigenvalues_finite (K : ℕ) : (ritzEigenvalues K).Finite := by
  let L : Module.End ℝ (Fin K → ℝ) := ((ritzMass K)⁻¹ * ritzStiffness K).mulVecLin
  apply (Module.End.finite_hasEigenvalue L).subset
  rintro μ ⟨c, hc, hμ⟩
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := c)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hc⟩
  change ((ritzMass K)⁻¹ * ritzStiffness K) *ᵥ c = μ • c
  rw [← mulVec_mulVec, hμ, mulVec_smul, mulVec_mulVec, nonsing_inv_mul, one_mulVec]
  exact (isUnit_iff_isUnit_det _).mp (ritzMass_posDef K).isUnit

theorem ritzEigenvalues_nonempty {K : ℕ} (hK : 0 < K) : (ritzEigenvalues K).Nonempty := by
  let d (i : Fin K) := (oddSectorFrequency i : ℝ) * π / 2
  have hd (i : Fin K) : 0 < d i := by
    have hi : 0 < oddSectorFrequency i := by unfold oddSectorFrequency; omega
    exact div_pos (mul_pos (by exact_mod_cast hi) pi_pos) (by norm_num)
  let D : Matrix (Fin K) (Fin K) ℝ := diagonal (fun i => (√(d i))⁻¹)
  have hd' (i : Fin K) : 0 < √(d i) := Real.sqrt_pos.mpr (hd i)
  have hD (u : Fin K → ℝ) (i : Fin K) : (D *ᵥ u) i = (√(d i))⁻¹ * u i :=
    mulVec_diagonal _ _ _
  have hDi : Function.Injective D.mulVec := by
    intro u v h
    funext i
    have he := congrFun h i
    rw [hD, hD] at he
    exact mul_left_cancel₀ (inv_ne_zero (hd' i).ne') he
  let H := Dᴴ * ritzMass K * D
  have hH : H.PosDef := (ritzMass_posDef K).conjTranspose_mul_mul_same hDi
  let j : Fin K := ⟨0, hK⟩
  let v : Fin K → ℝ := ⇑(hH.1.eigenvectorBasis j)
  let t := hH.1.eigenvalues j
  have ht : 0 < t := hH.eigenvalues_pos j
  have hv : v ≠ 0 := (ofLp_eq_zero 2).ne.2 <| hH.1.eigenvectorBasis.orthonormal.ne_zero j
  have he : H *ᵥ v = t • v := hH.1.mulVec_eigenvectorBasis j
  have hDstar : Dᴴ = D := isHermitian_diagonal_iff.mpr fun _ => star_trivial _
  have hev : D *ᵥ (ritzMass K *ᵥ (D *ᵥ v)) = t • v := by
    simpa only [H, ← mulVec_mulVec, hDstar] using he
  refine ⟨t⁻¹, D *ᵥ v, fun h => hv (hDi (h.trans (mulVec_zero D).symm)), ?_⟩
  funext i
  have h := congrFun hev i
  rw [hD] at h
  change (√(d i))⁻¹ * (ritzMass K *ᵥ (D *ᵥ v)) i = t * v i at h
  change (diagonal d *ᵥ (D *ᵥ v)) i = t⁻¹ * (ritzMass K *ᵥ (D *ᵥ v)) i
  rw [mulVec_diagonal, hD]
  have hs := Real.sq_sqrt (hd i).le
  field_simp [ht.ne', (hd' i).ne'] at h ⊢
  rw [h]
  linear_combination -(t * v i) * hs

/-- The actual least eigenvalue `a_K` of every nonempty finite pencil exists and is
an upper bound for the exact restricted second eigenvalue. -/
theorem exists_least_ritz_eigenvalue {K : ℕ} (hK : 0 < K) :
    ∃ aK, IsLeast (ritzEigenvalues K) aK ∧ Spectral.secondEigenvalue ≤ aK := by
  obtain ⟨μ, hμ, hm⟩ := Set.exists_min_image _ id (ritzEigenvalues_finite K) (ritzEigenvalues_nonempty hK)
  obtain ⟨c, hc, he⟩ := hμ
  exact ⟨μ, ⟨⟨c, hc, he⟩, hm⟩, secondEigenvalue_le_ritz hc he⟩

/-- The minimizing generalized eigenvector may be chosen with its physical
trial function normalized in `L²(ℝ)`. -/
theorem exists_normalized_least_ritz_eigenpair {K : ℕ} (hK : 0 < K) :
    ∃ (aK : ℝ) (c : Fin K → ℝ), IsLeast (ritzEigenvalues K) aK ∧ Spectral.secondEigenvalue ≤ aK ∧
      ritzStiffness K *ᵥ c = aK • (ritzMass K *ᵥ c) ∧ (∫ x : ℝ, ritzTrial c x ^ 2) = 1 := by
  obtain ⟨aK, hmin, ha⟩ := exists_least_ritz_eigenvalue hK
  obtain ⟨v, hv, hev⟩ := hmin.1
  let m := v ⬝ᵥ (ritzMass K *ᵥ v)
  have hm : 0 < m := by simpa [m] using (ritzMass_posDef K).dotProduct_mulVec_pos hv
  let s := (√m)⁻¹
  refine ⟨aK, s • v, hmin, ha, ?_, ?_⟩
  · rw [mulVec_smul, hev, mulVec_smul, smul_comm]
  · rw [ritzTrial_mass, mulVec_smul, smul_dotProduct, dotProduct_smul]
    change (√m)⁻¹ * ((√m)⁻¹ * m) = 1
    field_simp [(Real.sqrt_pos.mpr hm).ne']
    exact (Real.sq_sqrt hm.le).symm

end Torsion.Galerkin

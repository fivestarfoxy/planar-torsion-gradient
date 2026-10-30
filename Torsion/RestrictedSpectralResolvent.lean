module

public import Torsion.RestrictedSpectralGraphHilbert
public import Torsion.RestrictedSpectralCoreDirections
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The actual restricted Fourier-form resolvent

Lax--Milgram is applied to the constructed complete core-graph space and
the original frequency bilinear form. The resulting bounded operator on
actual real L² is positive and self-adjoint. Its spectral interpretation
uses the concrete coordinate/form identification, never a replacement PDE.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Torsion.Spectral.RestrictedHilbert

/-- The Lax--Milgram solution operator for arbitrary actual L² source data. -/
def solutionOperator : ValueL2 →L[ℝ] space :=
  energy_coercive.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp valueMap.adjoint

/-- Exact variational equation against every element of the actual graph. -/
theorem energy_solutionOperator (f : ValueL2) (q : space) :
    energy (solutionOperator f) q = inner (𝕜 := ℝ) f (valueMap q) := by
  calc
    _ = inner (𝕜 := ℝ) (energy_coercive.continuousLinearEquivOfBilin
        (solutionOperator f)) q :=
      (energy_coercive.continuousLinearEquivOfBilin_apply _ q).symm
    _ = inner (𝕜 := ℝ) (valueMap.adjoint f) q := by
      simp only [solutionOperator, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    _ = _ := valueMap.adjoint_inner_left q f

/-- Value of the actual weak restricted solution as an actual L² operator. -/
def resolvent : ValueL2 →L[ℝ] ValueL2 := valueMap.comp solutionOperator

theorem energy_symmetric (p q : space) : energy p q = energy q p := by
  rw [energy_apply, energy_apply, real_inner_comm]

theorem resolvent_isSymmetric : resolvent.toLinearMap.IsSymmetric := by
  intro f g
  calc
    inner (𝕜 := ℝ) (resolvent f) g = inner (𝕜 := ℝ) g (valueMap (solutionOperator f)) :=
      real_inner_comm _ _
    _ = energy (solutionOperator g) (solutionOperator f) :=
      (energy_solutionOperator g (solutionOperator f)).symm
    _ = energy (solutionOperator f) (solutionOperator g) := energy_symmetric _ _
    _ = inner (𝕜 := ℝ) f (resolvent g) := energy_solutionOperator f (solutionOperator g)

theorem resolvent_isSelfAdjoint : IsSelfAdjoint resolvent :=
  resolvent_isSymmetric.isSelfAdjoint

/-- Positivity is the actual positive Fourier energy of the weak solution. -/
theorem resolvent_nonneg (f : ValueL2) : 0 ≤ inner (𝕜 := ℝ) (resolvent f) f := by
  rw [real_inner_comm]
  change 0 ≤ inner (𝕜 := ℝ) f (valueMap (solutionOperator f))
  rw [← energy_solutionOperator f (solutionOperator f),
    energy_apply, real_inner_self_eq_norm_sq]
  positivity

/-- Vanishing of the diagonal actual energy forces the graph point to zero,
by the already proved quantitative coercivity. -/
theorem eq_zero_of_energy_self_eq_zero {p : space} (hp : energy p p = 0) : p = 0 := by
  obtain ⟨c, hc, hbound⟩ := energy_coercive
  have h := hbound p
  rw [hp] at h
  by_contra hne
  have hn : 0 < ‖p‖ := norm_pos_iff.mpr hne
  exact (not_le_of_gt (mul_pos (mul_pos hc hn) hn)) h

/-- If the value resolvent vanishes, the entire weak solution vanishes. -/
theorem solutionOperator_eq_zero_of_resolvent_eq_zero {f : ValueL2}
    (hf : resolvent f = 0) : solutionOperator f = 0 := by
  apply eq_zero_of_energy_self_eq_zero
  rw [energy_solutionOperator]
  change inner (𝕜 := ℝ) f (resolvent f) = 0
  rw [hf, inner_zero_right]

/-- No nonzero genuine form-domain source can be killed by the resolvent.
This statement is proved first for actual core sources without a density
or injectivity assumption. -/
theorem resolvent_core_ne_zero {f : ℝ → ℝ} (hf : IsCore f)
    (hne : ¬ f =ᵐ[volume] 0) : resolvent (hf.memLp_value.toLp f) ≠ 0 := by
  intro hz
  have hsol := solutionOperator_eq_zero_of_resolvent_eq_zero hz
  let q : space := ofMemRestrictedFormDomain hf.memRestrictedFormDomain
  have htest := energy_solutionOperator (hf.memLp_value.toLp f) q
  rw [hsol] at htest
  have he0 : energy (0 : space) q = (0 : ℝ) := by
    rw [energy_apply, halfMap.map_zero, inner_zero_left, mul_zero]
  rw [he0] at htest
  have hval : valueMap q = hf.memLp_value.toLp f := rfl
  rw [hval, real_inner_self_eq_norm_sq] at htest
  have hzero : hf.memLp_value.toLp f = 0 := norm_eq_zero.mp (eq_zero_of_pow_eq_zero htest.symm)
  apply hne
  exact hf.memLp_value.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hzero)

/-- The actual resolvent is a nonzero operator, witnessed by an explicit
nonzero even compact smooth source. -/
theorem resolvent_ne_zero : resolvent ≠ 0 := by
  intro hzero
  have h := resolvent_core_ne_zero evenCoreDirection_isCore evenCoreDirection_not_ae_zero
  exact h (by rw [hzero]; rfl)


/-- The variational solution satisfies the original restricted Fourier
weak equation against every original admissible function. -/
theorem solutionOperator_equation (f : ValueL2) {ψ : ℝ → ℝ}
    (hψ : MemRestrictedFormDomain ψ) :
    Torsion.Spectral.energy (resolvent f : ℝ → ℝ) ψ = ∫ x : ℝ, f x * ψ x := by
  have h := energy_solutionOperator f (ofMemRestrictedFormDomain hψ)
  rw [energy_eq_original_right, valueMap_ofMemRestrictedFormDomain, L2.inner_def] at h
  calc
    _ = ∫ x : ℝ, inner (𝕜 := ℝ) (f x) ((hψ.1.toLp ψ) x) := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hψ.1.coeFn_toLp] with x hx
      rw [hx]
      change ψ x * f x = f x * ψ x
      ring

/-- An actual nonzero resolvent eigenvector is an actual weak restricted
half-Laplacian eigenfunction, with reciprocal eigenvalue. -/
theorem isRestrictedEigenfunction_of_resolvent_eigenvector
    {μ : ℝ} {v : ValueL2} (hμ : μ ≠ 0) (hv0 : v ≠ 0)
    (hv : resolvent v = μ • v) :
    IsRestrictedEigenfunction (1 / μ) (v : ℝ → ℝ) := by
  have hae : (resolvent v : ℝ → ℝ) =ᵐ[volume] fun x => μ * v x := by
    rw [hv]
    simpa only [Pi.smul_apply, smul_eq_mul] using! Lp.coeFn_smul μ v
  have hscale : (fun x => μ⁻¹ * (resolvent v : ℝ → ℝ) x) =ᵐ[volume] (v : ℝ → ℝ) := by
    filter_upwards [hae] with x hx
    rw [hx]
    field_simp
  have hform := (memRestrictedFormDomain_coordinates (solutionOperator v)).const_mul μ⁻¹
  have hform' : MemRestrictedFormDomain (v : ℝ → ℝ) := hform.congr_ae hscale
  refine ⟨hform', (fun hz => hv0 (Lp.eq_zero_iff_ae_eq_zero.mpr hz)), ?_⟩
  intro ψ hψ
  have hweak := solutionOperator_equation v hψ
  rw [Torsion.Spectral.energy_congr_ae hae (Filter.EventuallyEq.rfl),
    Torsion.Spectral.energy_const_mul_left] at hweak
  calc
    _ = (∫ x : ℝ, v x * ψ x) / μ := by
      apply (eq_div_iff hμ).mpr
      simpa only [mul_comm] using hweak
    _ = _ := by ring

/-- The concrete resolvent really has at least two spectral directions:
every candidate first vector has an orthogonal source on which it is nonzero. -/
theorem resolvent_has_second_direction (v : ValueL2) :
    ∃ f : ValueL2, inner (𝕜 := ℝ) f v = 0 ∧ resolvent f ≠ 0 := by
  obtain ⟨f, hf, hne, horth⟩ := exists_core_nonzero_orthogonal (Lp.memLp v)
  refine ⟨hf.memLp_value.toLp f, ?_, resolvent_core_ne_zero hf hne⟩
  calc
    _ = ∫ x : ℝ, f x * v x := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.memLp_value.coeFn_toLp] with x hx
      rw [hx]
      change v x * f x = f x * v x
      ring
    _ = 0 := horth

end Torsion.Spectral.RestrictedHilbert

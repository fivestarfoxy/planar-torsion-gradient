module

public import Torsion.RestrictedSpectralCompactness
public import Torsion.RestrictedSpectralMinMax
public import Torsion.CompactSpectral

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Construction of the first two actual restricted eigenpairs

The actual form resolvent is compact, positive and self-adjoint. Two
independent actual compact smooth directions exclude rank one. Compact
spectral maximization and the proved reciprocal min--max inequalities
therefore construct normalized first and second variational eigenpairs
for the original concrete Fourier weak equation.

This does not yet prove strict separation or simplicity, nor identify the
second eigenfunction as odd, positive on the half-interval, concave or
Hölder continuous. Those are additional spectral property theorems.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Torsion.Spectral

/-- Compactness of the actual form embedding makes the actual weak
restricted resolvent a compact operator on real L². -/
theorem RestrictedHilbert.resolvent_isCompactOperator :
    IsCompactOperator (RestrictedHilbert.resolvent :
      RestrictedHilbert.ValueL2 → RestrictedHilbert.ValueL2) :=
  RestrictedHilbert.valueMap_isCompactOperator.comp_clm RestrictedHilbert.solutionOperator

/-- The original restricted Fourier problem has actual normalized first
and second variational eigenpairs. The lower bounds establish their order
in the original form, rather than merely providing two unrelated solutions.
Multiplicity is allowed; strict separation and the second profile's shape
are not asserted here. -/
theorem exists_first_two_restricted_eigenpairs :
    ∃ a₁ a₂ : ℝ, 0 < a₁ ∧ a₁ ≤ a₂ ∧
      ∃ φ₁ φ₂ : ℝ → ℝ,
        IsRestrictedEigenfunction a₁ φ₁ ∧ IsRestrictedEigenfunction a₂ φ₂ ∧
        (∫ x : ℝ, φ₁ x ^ 2) = 1 ∧ (∫ x : ℝ, φ₂ x ^ 2) = 1 ∧
        (∫ x : ℝ, φ₁ x * φ₂ x) = 0 ∧
        (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
          a₁ * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) ∧
        (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
          (∫ x : ℝ, φ₁ x * ψ x) = 0 →
            a₂ * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) := by
  obtain ⟨μ₁, μ₂, hμ₁, hμ₂, hμ₂₁, v₁, v₂, hv₁, hv₂, horth,
      he₁, he₂, hb₁, hb₂⟩ :=
    Torsion.CompactSelfAdjoint.exists_two_positive_eigenpairs
      RestrictedHilbert.resolvent RestrictedHilbert.resolvent_isSelfAdjoint
      RestrictedHilbert.resolvent_isCompactOperator
      RestrictedHilbert.resolvent_nonneg RestrictedHilbert.resolvent_has_second_direction
  have hv₁ne : v₁ ≠ 0 := by intro h; simp [h] at hv₁
  have hv₂ne : v₂ ≠ 0 := by intro h; simp [h] at hv₂
  have hE₁ := RestrictedHilbert.isRestrictedEigenfunction_of_resolvent_eigenvector
    hμ₁.ne' hv₁ne he₁
  have hE₂ := RestrictedHilbert.isRestrictedEigenfunction_of_resolvent_eigenvector
    hμ₂.ne' hv₂ne he₂
  refine ⟨1 / μ₁, 1 / μ₂, one_div_pos.mpr hμ₁, ?_, v₁, v₂,
    hE₁, hE₂, ?_, ?_, ?_, ?_, ?_⟩
  · apply (div_le_div_iff₀ hμ₁ hμ₂).mpr
    simpa only [one_mul] using hμ₂₁
  · rw [integral_sq_eq_norm_toLp_sq (Lp.memLp v₁), Lp.toLp_coeFn, hv₁]
    norm_num
  · rw [integral_sq_eq_norm_toLp_sq (Lp.memLp v₂), Lp.toLp_coeFn, hv₂]
    norm_num
  · calc
      (∫ x : ℝ, v₁ x * v₂ x) = inner (𝕜 := ℝ) v₁ v₂ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by change v₁ x * v₂ x = v₂ x * v₁ x; ring
      _ = 0 := horth
  · intro ψ hψ
    exact hψ.energy_ge_of_resolvent_quadratic_bound_at hμ₁ (hb₁ _)
  · intro ψ hψ hψorth
    have hh : inner (𝕜 := ℝ) v₁ (hψ.1.toLp ψ) = 0 := by
      calc
        _ = ∫ x : ℝ, v₁ x * ψ x := by
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards [hψ.1.coeFn_toLp] with x hx
          rw [hx]
          change ψ x * v₁ x = v₁ x * ψ x
          ring
        _ = 0 := hψorth
    exact hψ.energy_ge_of_resolvent_quadratic_bound_at hμ₂ (hb₂ _ hh)



end Torsion.Spectral

import Torsion.RestrictedSpectralEigenpairs
import Torsion.RestrictedSpectralMinimizer
import Torsion.CompactSpectral.SecondAfterFirst

/-!
# An actual even nonnegative normalized restricted ground state

The first variational eigenpair is constructed by the actual compact
restricted resolvent. The genuine absolute-value contraction and reflection
then provide an even pointwise nonnegative normalized ground choice, with
its original global Rayleigh lower bound. Strict positivity and simplicity
are not assumed or concluded here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- The original restricted Fourier problem has an actual normalized even,
pointwise nonnegative ground eigenfunction and a genuine global minimum
Rayleigh bound. No spectral input is supplied as an assumption. -/
theorem exists_even_nonnegative_ground_eigenfunction :
    ∃ a : ℝ, 0 < a ∧ ∃ φ : ℝ → ℝ,
      IsRestrictedEigenfunction a φ ∧ Function.Even φ ∧
      (∀ x : ℝ, 0 ≤ φ x) ∧ (∫ x : ℝ, φ x ^ 2) = 1 ∧
      (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
        a * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) := by
  obtain ⟨a₁, a₂, ha₁, ha₁₂, φ₁, φ₂, hφ₁, hφ₂, hn₁, hn₂, horth, hlower, hsecond⟩ :=
    exists_first_two_restricted_eigenpairs
  obtain ⟨φ, hφ, heven, hnonneg, hnorm⟩ :=
    hφ₁.exists_even_nonnegative_normalized hlower
  exact ⟨a₁, ha₁, φ, hφ, heven, hnonneg, hnorm, hlower⟩

namespace RestrictedHilbert

/-- Every actual weak restricted eigenfunction gives a reciprocal
resolvent eigenvector in its original real L² class. -/
theorem resolvent_eigenvector_of_isRestrictedEigenfunction
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) :
    resolvent (hf.1.1.toLp f) = (1 / a) • (hf.1.1.toLp f) := by
  let F : ValueL2 := hf.1.1.toLp f
  let q : space := ofMemRestrictedFormDomain hf.1
  have hq (p : space) : energy q p = a * inner (𝕜 := ℝ) F (valueMap p) := by
    calc
      _ = Torsion.Spectral.energy f (valueMap p : ℝ → ℝ) := by
        rw [energy_symmetric, energy_eq_original_right, Torsion.Spectral.energy_symm]
      _ = a * ∫ x : ℝ, f x * valueMap p x :=
        hf.2.2 _ (memRestrictedFormDomain_coordinates p)
      _ = _ := by
        congr 1
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hf.1.1.coeFn_toLp] with x hx
        change f x * valueMap p x = inner (𝕜 := ℝ) (F x) (valueMap p x)
        rw [hx]
        change f x * valueMap p x = valueMap p x * f x
        ring
  have hscaled (p : space) : energy ((1 / a) • q) p = inner (𝕜 := ℝ) F (valueMap p) := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hq]
    field_simp [hf.eigenvalue_pos.ne']
  have hsol : solutionOperator F = (1 / a) • q := by
    apply energy_coercive.continuousLinearEquivOfBilin.injective
    apply ext_inner_right ℝ
    intro p
    rw [energy_coercive.continuousLinearEquivOfBilin_apply,
      energy_coercive.continuousLinearEquivOfBilin_apply, energy_solutionOperator, hscaled]
  change valueMap (solutionOperator F) = (1 / a) • F
  rw [hsol, map_smul]
  rfl

/-- A global lower bound for the original Fourier form supplies the
reciprocal quadratic upper bound for the actual value resolvent. -/
theorem resolvent_quadratic_bound_of_form_lower_bound {a : ℝ} (ha : 0 < a)
    (hlower : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      a * (∫ x : ℝ, ψ x ^ 2) ≤ Torsion.Spectral.energy ψ ψ) (F : ValueL2) :
    inner (𝕜 := ℝ) (resolvent F) F ≤ (1 / a) * ‖F‖ ^ 2 := by
  let q : space := solutionOperator F
  let w : ValueL2 := resolvent F
  have hl : a * ‖w‖ ^ 2 ≤ inner (𝕜 := ℝ) F w := by
    have h := hlower (valueMap q : ℝ → ℝ) (memRestrictedFormDomain_coordinates q)
    rw [integral_sq_eq_norm_toLp_sq (Lp.memLp (valueMap q)), Lp.toLp_coeFn,
      ← energy_eq_original, energy_solutionOperator] at h
    exact h
  by_cases hw : w = 0
  · change inner (𝕜 := ℝ) w F ≤ (1 / a) * ‖F‖ ^ 2
    rw [hw, inner_zero_left]
    positivity
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hcs : inner (𝕜 := ℝ) F w ≤ ‖F‖ * ‖w‖ := real_inner_le_norm F w
  have hmul : a * ‖w‖ ≤ ‖F‖ := by
    apply (mul_le_mul_right hwpos).mp
    nlinarith [hl, hcs]
  have hwnorm : ‖w‖ ≤ ‖F‖ / a :=
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hmul)
  calc
    _ = inner (𝕜 := ℝ) F w := real_inner_comm _ _
    _ ≤ ‖F‖ * ‖w‖ := hcs
    _ ≤ ‖F‖ * (‖F‖ / a) := mul_le_mul_of_nonneg_left hwnorm (norm_nonneg F)
    _ = _ := by ring

end RestrictedHilbert

/-- The first two variational eigenpairs can be constructed with an even,
pointwise nonnegative normalized first profile. The second eigenfunction
is selected anew in the orthogonal complement of this exact ground choice,
so its orthogonality and min--max bound are proved for the stated pair. -/
theorem exists_first_two_restricted_eigenpairs_even_nonnegative_first :
    ∃ a₁ a₂ : ℝ, 0 < a₁ ∧ a₁ ≤ a₂ ∧
      ∃ φ₁ φ₂ : ℝ → ℝ,
        IsRestrictedEigenfunction a₁ φ₁ ∧ IsRestrictedEigenfunction a₂ φ₂ ∧
        (∫ x : ℝ, φ₁ x ^ 2) = 1 ∧ (∫ x : ℝ, φ₂ x ^ 2) = 1 ∧
        (∫ x : ℝ, φ₁ x * φ₂ x) = 0 ∧ Function.Even φ₁ ∧
        (∀ x : ℝ, 0 ≤ φ₁ x) ∧
        (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
          a₁ * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) ∧
        (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
          (∫ x : ℝ, φ₁ x * ψ x) = 0 →
            a₂ * (∫ x : ℝ, ψ x ^ 2) ≤ energy ψ ψ) := by
  obtain ⟨a, ha, φ, hφ, heven, hnonneg, hnorm⟩ := exists_even_nonnegative_ground_eigenfunction
  obtain ⟨hnorm, hlower⟩ := hnorm
  let F : RestrictedHilbert.ValueL2 := hφ.1.1.toLp φ
  have hfirst : ∀ z : RestrictedHilbert.ValueL2,
      RestrictedHilbert.resolvent.reApplyInnerSelf z ≤ (1 / a) * ‖z‖ ^ 2 :=
    RestrictedHilbert.resolvent_quadratic_bound_of_form_lower_bound ha hlower
  obtain ⟨μ₂, hμ₂, hμ₂₁, v₂, hv₂, horth, he₂, hb₂⟩ :=
    Torsion.CompactSelfAdjoint.exists_positive_second_after_first
      RestrictedHilbert.resolvent RestrictedHilbert.resolvent_isSelfAdjoint
      RestrictedHilbert.resolvent_isCompactOperator RestrictedHilbert.resolvent_nonneg
      RestrictedHilbert.resolvent_has_second_direction
      (RestrictedHilbert.resolvent_eigenvector_of_isRestrictedEigenfunction hφ) hfirst
  have hv₂ne : v₂ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv₂
    norm_num at hv₂
  have hE₂ := RestrictedHilbert.isRestrictedEigenfunction_of_resolvent_eigenvector
    hμ₂.ne' hv₂ne he₂
  refine ⟨a, 1 / μ₂, ha, ?_, φ, v₂, hφ, hE₂, hnorm, ?_, ?_, heven,
    hnonneg, hlower, ?_⟩
  · apply (le_div_iff₀ hμ₂).mpr
    calc
      a * μ₂ ≤ a * (1 / a) := mul_le_mul_of_nonneg_left hμ₂₁ ha.le
      _ = 1 := by field_simp [ha.ne']
  · rw [integral_sq_eq_norm_toLp_sq (Lp.memLp v₂), Lp.toLp_coeFn, hv₂]
    norm_num
  · calc
      (∫ x : ℝ, φ x * v₂ x) = inner (𝕜 := ℝ) F v₂ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hφ.1.1.coeFn_toLp] with x hx
        change φ x * v₂ x = inner (𝕜 := ℝ) (F x) (v₂ x)
        rw [hx]
        change φ x * v₂ x = v₂ x * φ x
        ring
      _ = 0 := horth
  · intro ψ hψ hψorth
    have hh : inner (𝕜 := ℝ) F (hψ.1.toLp ψ) = 0 := by
      calc
        _ = ∫ x : ℝ, φ x * ψ x := by
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards [hφ.1.1.coeFn_toLp, hψ.1.coeFn_toLp] with x hx hψx
          change inner (𝕜 := ℝ) (F x) ((hψ.1.toLp ψ) x) = φ x * ψ x
          rw [hx, hψx]
          change ψ x * φ x = φ x * ψ x
          ring
        _ = 0 := hψorth
    exact hψ.energy_ge_of_resolvent_quadratic_bound_at hμ₂ (hb₂ _ hh)

end Torsion.Spectral

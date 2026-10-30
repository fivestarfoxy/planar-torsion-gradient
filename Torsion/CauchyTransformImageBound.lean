module

public import Torsion.CauchyTransformBoundaryExtension
public import Torsion.CauchyQuadraticIdentity
public import Torsion.SpectralNormalization

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Boundedness of the actual Cauchy image

The integrated profile is Lipschitz, so its actual Cauchy transform has the
continuous closed-half-plane extension proved above. Compactness bounds that
extension in a fixed ball; the explicit integral estimate bounds every
exterior point. No bounded-image certificate is assumed.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The concrete spectral map has a genuine finite global norm bound.
Continuity, oddness and zero exterior values suffice; no eigenfunction
equation, univalence or geometric regularity is used. -/
theorem cauchy_exists_norm_bound {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ upperHalfPlane, ‖cauchy φ z‖ ≤ B := by
  obtain ⟨CY, hY⟩ := height_exists_holder (α := 1) hφ hodd hzero le_rfl
  have hF := (cauchyExtension_diffContOnCl hY (by norm_num)).continuousOn
  have hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ upperHalfPlane, ‖cauchyExtension φ z‖ ≤ B := by
    apply bounded_on_upperHalfPlane_of_continuousOn_closure hF
      (‖(Real.pi : ℂ)⁻¹‖ * (∫ s in Icc (-1 : ℝ) 1, ‖(height φ s : ℂ)‖))
    intro z hz hn
    rw [cauchyExtension_eq hφ.continuousOn hz]
    unfold cauchy
    rw [norm_mul, norm_neg]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_cauchy_integral_le
      (Complex.continuous_ofReal.comp (height_continuous hφ.continuousOn)).continuousOn
      (by linarith : 1 < ‖z‖)).trans
    exact div_le_self (integral_nonneg fun _ => norm_nonneg _) (by linarith)
  obtain ⟨B, hB0, hB⟩ := hbound
  refine ⟨B, hB0, ?_⟩
  intro z hz
  simpa only [cauchyExtension_eq hφ.continuousOn hz] using hB z hz

/-- The unnormalized image in the source construction is actually bounded. -/
theorem cauchy_image_isBounded {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    Bornology.IsBounded (cauchy φ '' upperHalfPlane) := by
  obtain ⟨B, _, hB⟩ := cauchy_exists_norm_bound hφ hodd hzero
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨B, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hB z hz

/-- Consequently its planar area is finite before the exact area formula
has been established. -/
theorem volume_cauchy_image_lt_top {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    volume (cauchy φ '' upperHalfPlane) < ⊤ :=
  (cauchy_image_isBounded hφ hodd hzero).measure_lt_top

/-- Normalization preserves genuine boundedness for every value of the
normalization scalar, including the total-formula degenerate cases. -/
theorem normalizedImage_isBounded (a : ℝ) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    Bornology.IsBounded (normalizedImage a φ) := by
  obtain ⟨B, hB0, hB⟩ := cauchy_exists_norm_bound hφ hodd hzero
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨‖(((Real.sqrt (a * squareMass φ / 2))⁻¹ : ℝ) : ℂ)‖ * B, ?_⟩
  rintro _ ⟨w, ⟨z, hz, rfl⟩, rfl⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB z hz) (norm_nonneg _)

/-- The same compactness and exterior-kernel argument bounds the actual
Cauchy integral of any Hölder zero-exterior density. -/
theorem realCauchy_exists_norm_bound {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → f x = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ upperHalfPlane, ‖realCauchy f z‖ ≤ B := by
  have hcont := hf.continuous hα
  obtain ⟨B, hB0, hB⟩ := bounded_on_upperHalfPlane_of_continuousOn_closure
    (realCauchyExtension_continuousOn hf hα hzero)
    (‖(Real.pi : ℂ)⁻¹‖ * (∫ s in Icc (-1 : ℝ) 1, ‖(f s : ℂ)‖))
    (fun z hz hn => by
      rw [realCauchyExtension_eq hcont hzero hz]
      unfold realCauchy
      rw [norm_mul, norm_neg]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (norm_cauchy_integral_le (Complex.continuous_ofReal.comp hcont).continuousOn
        (by linarith : 1 < ‖z‖)).trans
      exact div_le_self (integral_nonneg fun _ => norm_nonneg _) (by linarith))
  exact ⟨B, hB0, fun z hz => by
    simpa only [realCauchyExtension_eq hcont hzero hz] using hB z hz⟩

/-- The auxiliary transform is genuinely bounded as well. This supplies a
finite value bound for the explicit torsion candidate built from F and A. -/
theorem auxiliary_exists_norm_bound {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ upperHalfPlane, ‖auxiliary φ z‖ ≤ B := by
  obtain ⟨CY, hY⟩ := height_exists_holder (α := 1) hφ hodd hzero le_rfl
  obtain ⟨BY, hBY⟩ := exists_nnreal_bound_of_compactSupport
    (height_continuous hφ.continuousOn) (height_hasCompactSupport φ)
  have hYsq : HolderWith (BY * CY + BY * CY) 1 (fun s => (height φ s) ^ 2) := by
    simpa only [pow_two] using holderWith_mul_of_bounded hY hY hBY hBY
  obtain ⟨B, hB0, hB⟩ := realCauchy_exists_norm_bound hYsq (by norm_num)
    (fun s hs => by rw [height_zero_of_one_le_abs φ hs]; norm_num)
  refine ⟨‖(1 / 2 : ℂ)‖ * B, mul_nonneg (norm_nonneg _) hB0, ?_⟩
  intro z hz
  have heq : auxiliary φ z = (1 / 2 : ℂ) * realCauchy (fun s => (height φ s) ^ 2) z := by
    unfold auxiliary realCauchy
    simp only [mul_inv_rev]
    ring
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_left (hB z hz) (norm_nonneg _)

end Torsion.Spectral


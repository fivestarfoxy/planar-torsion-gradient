module

public import Torsion.PaperGeometry
public import Torsion.PaperLipschitz

@[expose] public section

/-! # The physical flat side and its maximum inward slope at area one -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Torsion.Spectral

/-- The positive endpoint of the unnormalized straight side. -/
def secondUnscaledFlatHalfWidth : ℝ :=
  Real.pi⁻¹ * ∫ s in Icc (-1 : ℝ) 1, height secondEigenfunction s / (1 - s)

private theorem real_mem_frontier_cauchy_iff (x : ℝ) :
    (x : ℂ) ∈ frontier (cauchyImage secondEigenfunction) ↔ |x| ≤ secondUnscaledFlatHalfWidth := by
  obtain ⟨hℓ, hm, hp⟩ := secondFreeArc_endpoints
  change 0 < secondUnscaledFlatHalfWidth at hℓ
  change cauchyExtension secondEigenfunction (-1 : ℂ) = (secondUnscaledFlatHalfWidth : ℂ) at hm
  change cauchyExtension secondEigenfunction (1 : ℂ) = -(secondUnscaledFlatHalfWidth : ℂ) at hp
  rw [frontier_cauchyImage_freeArc_union_segment secondHolderConstant_spec half_pos_nnreal
    half_le_one_nnreal secondEigenfunction_odd secondEigenfunction_zero_exterior secondEigenfunction_pos,
    hm, hp, Complex.neg_re, Complex.ofReal_re]
  constructor
  · rintro (⟨t, ht, htx⟩ | ⟨y, hy, hxy⟩)
    · rcases eq_or_lt_of_le ht.1 with hleft | hleft
      · subst t
        simp only [Complex.ofReal_neg, Complex.ofReal_one] at htx
        rw [hm, Complex.ofReal_inj] at htx
        simp [← htx, abs_of_pos hℓ]
      rcases eq_or_lt_of_le ht.2 with hright | hright
      · subst t
        simp only [Complex.ofReal_one] at htx
        rw [hp, ← Complex.ofReal_neg, Complex.ofReal_inj] at htx
        simp [← htx, abs_of_pos hℓ]
      · exact ((Set.disjoint_left.mp
          (cauchy_freeArc_disjoint_realAxis secondEigenfunction_continuous.continuousOn
            secondEigenfunction_pos)) ⟨t, ⟨hleft, hright⟩, htx⟩ ⟨x, rfl⟩).elim
    · exact abs_le.mpr ((Complex.ofReal_inj.mp hxy) ▸ hy)
  · intro hx
    exact Or.inr ⟨x, abs_le.mp hx, rfl⟩

/-- The normalized half-width is the Cauchy endpoint integral divided by
the square root of the unscaled area. -/
def normalizedFlatHalfWidth : ℝ :=
  (Real.sqrt secondMoments.area)⁻¹ * secondUnscaledFlatHalfWidth

theorem normalizedFlatHalfWidth_pos : 0 < normalizedFlatHalfWidth :=
  mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr secondMoments.area_pos)) secondFreeArc_endpoints.1

/-- The two endpoints have physical distance twice the half-width, and
their affine midpoint is the marked origin. -/
theorem normalizedFlatSide_length_midpoint :
    dist (-(normalizedFlatHalfWidth : ℂ)) (normalizedFlatHalfWidth : ℂ) =
        2 * normalizedFlatHalfWidth ∧
      midpoint ℝ (-(normalizedFlatHalfWidth : ℂ)) (normalizedFlatHalfWidth : ℂ) = 0 := by
  refine ⟨?_, midpoint_neg_self ℝ _⟩
  rw [dist_eq_norm, ← Complex.ofReal_neg, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith [normalizedFlatHalfWidth_pos])]
  ring

/-- Exactly the real interval from minus to plus the normalized half-width
belongs to the frontier of the normalized spectral domain. -/
theorem real_mem_frontier_normalizedImage_iff (x : ℝ) :
    (x : ℂ) ∈ frontier (normalizedImage secondEigenvalue secondEigenfunction) ↔
      |x| ≤ normalizedFlatHalfWidth := by
  let s := (Real.sqrt secondMoments.area)⁻¹
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr secondMoments.area_pos)
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero s hs.ne'
  have hset : normalizedImage secondEigenvalue secondEigenfunction =
      e '' cauchyImage secondEigenfunction := by
    unfold normalizedImage
    have harea : secondEigenvalue * squareMass secondEigenfunction / 2 = secondMoments.area :=
      secondMoments.area_eq.symm
    rw [harea]
    rfl
  have hcoord : e ((x / s : ℝ) : ℂ) = (x : ℂ) := by
    change s • ((x / s : ℝ) : ℂ) = _
    rw [Complex.real_smul, ← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [hset, ← e.image_frontier, ← hcoord, e.injective.mem_set_image,
    real_mem_frontier_cauchy_iff, abs_div, abs_of_pos hs, div_le_iff₀ hs]
  change _ ≤ secondUnscaledFlatHalfWidth * s ↔ _ ≤ s * secondUnscaledFlatHalfWidth
  rw [mul_comm secondUnscaledFlatHalfWidth]

/-- The midpoint of the entire flat side has inward torsion quotient equal
to the maximum weak-gradient norm on the unit-area domain. -/
theorem second_flat_midpoint_has_sharp_quotient :
    ∃ (D : ConvexDomain) (U : Plane → ℝ) (g : Plane → Plane),
      D.carrier = normalizedImage secondEigenvalue secondEigenfunction ∧ D.area = 1 ∧
      (∀ x : ℝ, (x : ℂ) ∈ frontier D.carrier ↔ |x| ≤ normalizedFlatHalfWidth) ∧
      IsWeakTorsion D.carrier U g ∧ HasMarkedFlux U (torsionTheory.G D).toReal ∧
      (torsionTheory.G D).toReal = spectralConstant secondEigenvalue secondEigenfunction := by
  obtain ⟨D, U, g, hD, hA, hu, _, _, hq, _, _, _⟩ := second_lipschitz_and_distance_sharp
  obtain ⟨D', hD', _, hG⟩ := second_exact_value.2
  have hDD : D = D' := by
    cases D; cases D'; cases hD.trans hD'.symm; rfl
  subst D'
  have heq : (torsionTheory.G D).toReal =
      spectralConstant secondEigenvalue secondEigenfunction := by
    rw [hG]
    exact ENNReal.toReal_ofReal secondMoments.sharpConstant_pos.le
  refine ⟨D, U, g, hD, hA, ?_, hu, heq.symm ▸ hq, heq⟩
  intro x
  rw [hD]
  exact real_mem_frontier_normalizedImage_iff x

end Torsion.Spectral

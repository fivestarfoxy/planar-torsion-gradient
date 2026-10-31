module

public import Torsion.ContinuousProfiles
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Symmetric difference of actual radial domains

The positive continuous profiles determine genuine subsets of the complex
plane. Their union and intersection have the pointwise maximum and minimum
profiles. The proved polar-area formula and Cauchy--Schwarz therefore control
their symmetric-difference area by the angular `L²` profile distance.

No torsion, calibration, or shape-derivative hypotheses occur in this module.
-/

noncomputable section

namespace Torsion.ContinuousProfiles

open Set MeasureTheory
open scoped ENNReal symmDiff

private theorem extend_sup_apply (R S : Profile) (θ : ℝ) :
    extend (R ⊔ S) θ = max (extend R θ) (extend S θ) := rfl

private theorem extend_inf_apply (R S : Profile) (θ : ℝ) :
    extend (R ⊓ S) θ = min (extend R θ) (extend S θ) := rfl

/-- Taking the maximum radius takes the union of the actual domains. -/
theorem radialDomain_sup (R S : Profile) :
    radialDomain (extend (R ⊔ S)) =
      radialDomain (extend R) ∪ radialDomain (extend S) := by
  ext z
  simp only [RadialGeometry.mem_radialDomain_iff, Set.mem_union, extend_sup_apply,
    lt_max_iff]
  tauto

/-- Taking the minimum radius takes the intersection of the actual domains. -/
theorem radialDomain_inf (R S : Profile) :
    radialDomain (extend (R ⊓ S)) =
      radialDomain (extend R) ∩ radialDomain (extend S) := by
  ext z
  simp only [RadialGeometry.mem_radialDomain_iff, Set.mem_inter_iff, extend_inf_apply,
    lt_min_iff]
  tauto

private theorem sup_inf_add (R S : Profile) : (R ⊔ S) + (R ⊓ S) = R + S := by
  ext θ
  change max (R θ) (S θ) + min (R θ) (S θ) = R θ + S θ
  rcases le_total (R θ) (S θ) with h | h
  · rw [max_eq_right h, min_eq_left h, add_comm]
  · rw [max_eq_left h, min_eq_right h]

private theorem norm_sub_sup_inf (R S : Profile) :
    ‖embed (R ⊔ S) - embed (R ⊓ S)‖ = ‖embed R - embed S‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [norm_sq_sub_embed, norm_sq_sub_embed]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [extend_sup_apply, extend_inf_apply]
  rcases le_total (extend R θ) (extend S θ) with h | h
  · rw [max_eq_right h, min_eq_left h]
    ring
  · rw [max_eq_left h, min_eq_right h]

/-- The true planar symmetric-difference area is a difference of the two
polar areas, including all contributions near the horizontal directions. -/
theorem area_symmDiff_eq_profileArea_sub {R S : Profile}
    (hR : ∀ θ, 0 < R θ) (hS : ∀ θ, 0 < S θ) :
    (volume (radialDomain (extend R) ∆ radialDomain (extend S))).toReal =
      Calibration.profileArea (embed (R ⊔ S)) -
        Calibration.profileArea (embed (R ⊓ S)) := by
  have hsup : ∀ θ, 0 < (R ⊔ S) θ := fun θ => (hR θ).trans_le (le_max_left _ _)
  have hinf : ∀ θ, 0 < (R ⊓ S) θ := fun θ => lt_min (hR θ) (hS θ)
  have hset : radialDomain (extend R) ∆ radialDomain (extend S) =
      radialDomain (extend (R ⊔ S)) \ radialDomain (extend (R ⊓ S)) := by
    rw [radialDomain_sup, radialDomain_inf]
    ext z
    simp only [Set.mem_symmDiff, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  have hsub : radialDomain (extend (R ⊓ S)) ⊆ radialDomain (extend (R ⊔ S)) := by
    rw [radialDomain_sup, radialDomain_inf]
    exact inter_subset_left.trans subset_union_left
  have hmeas : MeasurableSet (radialDomain (extend (R ⊓ S))) :=
    (RadialGeometry.radialDomain_isOpen (extend (R ⊓ S)).continuous.continuousOn).measurableSet
  have hfin : volume (radialDomain (extend (R ⊔ S))) ≠ ∞ := by
    rw [RadialGeometry.volume_radialDomain (extend (R ⊔ S)).continuous.continuousOn]
    · exact ENNReal.ofReal_ne_top
    · intro θ hθ
      change 0 < extend (R ⊔ S) (⟨θ, hθ⟩ : Angle)
      rw [extend_coe]
      exact hsup _
  rw [hset]
  change volume.real _ = _
  rw [measureReal_sdiff hsub hmeas hfin]
  exact congrArg₂ (· - ·) (geometric_area_eq_profileArea hsup)
    (geometric_area_eq_profileArea hinf)

/-- Cauchy--Schwarz bounds the genuine geometric symmetric difference using
the angular `L²` norms. Both domains retain the same marked origin and half-plane. -/
theorem area_symmDiff_le_l2 {R S : Profile}
    (hR : ∀ θ, 0 < R θ) (hS : ∀ θ, 0 < S θ) :
    (volume (radialDomain (extend R) ∆ radialDomain (extend S))).toReal ≤
      (1 / 2 : ℝ) * ‖embed R - embed S‖ * ‖embed R + embed S‖ := by
  have hid : inner (𝕜 := ℝ) (embed (R ⊔ S) - embed (R ⊓ S))
      (embed (R ⊔ S) + embed (R ⊓ S)) =
      ‖embed (R ⊔ S)‖ ^ 2 - ‖embed (R ⊓ S)‖ ^ 2 := by
    simp only [inner_sub_left, inner_add_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm (embed (R ⊓ S)) (embed (R ⊔ S))]
    ring
  have hbound := real_inner_le_norm (embed (R ⊔ S) - embed (R ⊓ S))
    (embed (R ⊔ S) + embed (R ⊓ S))
  rw [hid, norm_sub_sup_inf, ← map_add, sup_inf_add, map_add] at hbound
  rw [area_symmDiff_eq_profileArea_sub hR hS]
  unfold Calibration.profileArea
  linarith

/-- For area-one actual radial domains, squared symmetric-difference area
is at most twice the squared angular `L²` distance. -/
theorem area_one_symmDiff_sq_le {R S : Profile}
    (hR : ∀ θ, 0 < R θ) (hS : ∀ θ, 0 < S θ)
    (hAR : radialArea (extend R) = 1) (hAS : radialArea (extend S) = 1) :
    (volume (radialDomain (extend R) ∆ radialDomain (extend S))).toReal ^ 2 ≤
      2 * ‖embed R - embed S‖ ^ 2 := by
  have hRnorm : ‖embed R‖ ^ 2 = 2 := by
    rw [norm_sq_eq_twice_radialArea, hAR]
    ring
  have hSnorm : ‖embed S‖ ^ 2 = 2 := by
    rw [norm_sq_eq_twice_radialArea, hAS]
    ring
  have hsum := norm_add_le (embed R) (embed S)
  have hsum_nonneg := norm_nonneg (embed R + embed S)
  have hR_nonneg := norm_nonneg (embed R)
  have hS_nonneg := norm_nonneg (embed S)
  have hnorms : ‖embed R‖ = ‖embed S‖ :=
    (sq_eq_sq₀ hR_nonneg hS_nonneg).1 (hRnorm.trans hSnorm.symm)
  have hsum_sq : ‖embed R + embed S‖ ^ 2 ≤ 8 := by
    rw [← hnorms] at hsum
    nlinarith
  have hbound := area_symmDiff_le_l2 hR hS
  have harea_nonneg : 0 ≤
      (volume (radialDomain (extend R) ∆ radialDomain (extend S))).toReal :=
    ENNReal.toReal_nonneg
  have hdiff_nonneg := norm_nonneg (embed R - embed S)
  have hsquare := mul_self_le_mul_self harea_nonneg hbound
  have hprod := mul_le_mul_of_nonneg_left hsum_sq (sq_nonneg ‖embed R - embed S‖)
  nlinarith

/-- The same estimate stated entirely with genuine planar areas and an
ordinary angular integral, rather than the Hilbert-space area model. -/
theorem geometric_area_one_symmDiff_sq_le {R S : Profile}
    (hR : ∀ θ, 0 < R θ) (hS : ∀ θ, 0 < S θ)
    (hAR : (volume (radialDomain (extend R))).toReal = 1)
    (hAS : (volume (radialDomain (extend S))).toReal = 1) :
    (volume (radialDomain (extend R) ∆ radialDomain (extend S))).toReal ^ 2 ≤
      2 * (∫ θ in Ioo (0 : ℝ) Real.pi, (extend R θ - extend S θ) ^ 2) := by
  have hRarea : radialArea (extend R) = 1 := by
    rw [← profileArea_embed, ← geometric_area_eq_profileArea hR]
    exact hAR
  have hSarea : radialArea (extend S) = 1 := by
    rw [← profileArea_embed, ← geometric_area_eq_profileArea hS]
    exact hAS
  simpa only [norm_sq_sub_embed] using area_one_symmDiff_sq_le hR hS hRarea hSarea

end Torsion.ContinuousProfiles

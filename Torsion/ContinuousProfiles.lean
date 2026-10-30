import Torsion.Definitions
import Torsion.RadialGeometry
import Torsion.RadialStability
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Continuous radial profiles and the concrete L² space

The angle space is the closed interval `[0, π]`, equipped with Lebesgue
measure restricted to that subtype. Its endpoints are retained in the
continuous profile, although they have measure zero. The embedding into
`L²` is injective, including at those endpoints.
-/

noncomputable section

namespace Torsion.ContinuousProfiles

open MeasureTheory Set
open scoped NNReal ENNReal
open Torsion.Calibration Torsion.Stability

/-- Closed angular interval, so a profile includes its endpoint values. -/
abbrev Angle := Icc (0 : ℝ) Real.pi

/-- Continuous radial profiles on the entire closed angular interval. -/
abbrev Profile := C(Angle, ℝ)

/-- Lebesgue measure on the interval subtype. -/
def angleMeasure : Measure Angle := Measure.comap Subtype.val volume

instance : IsFiniteMeasure angleMeasure where
  measure_univ_lt_top := by
    rw [angleMeasure, comap_subtype_coe_apply measurableSet_Icc]
    have himg : Subtype.val '' (univ : Set Angle) = Icc (0 : ℝ) Real.pi := by
      ext θ
      simp
    rw [himg]
    exact measure_Icc_lt_top

/-- Concrete real Hilbert space of square-integrable angular profiles. -/
abbrev ProfileL2 := Lp ℝ 2 angleMeasure

/-- The actual continuous-linear embedding into `L²`. -/
def embed : Profile →L[ℝ] ProfileL2 := ContinuousMap.toLp 2 angleMeasure ℝ

/-- Extend the continuous profile constantly past its two endpoints. This is
only used to state ordinary real-variable integrals and radial domains. -/
def extend (R : Profile) : C(ℝ, ℝ) := ContinuousMap.IccExtend Real.pi_pos.le R

@[simp]
theorem extend_coe (R : Profile) (θ : Angle) : extend R θ = R θ := by
  simp [extend, ContinuousMap.IccExtend, Set.IccExtend, Set.projIcc, θ.property.1, θ.property.2]

/-- Equality in `L²` gives equality of the original continuous profiles,
including θ = 0 and θ = π. -/
theorem embed_injective : Function.Injective embed := by
  intro R S hRS
  have hR := ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) angleMeasure R
  have hS := ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) angleMeasure S
  have hae : (R : Angle → ℝ) =ᵐ[angleMeasure] S := by
    filter_upwards [hR, hS] with θ hRθ hSθ
    change (embed R : Angle → ℝ) θ = R θ at hRθ
    change (embed S : Angle → ℝ) θ = S θ at hSθ
    rw [hRS] at hRθ
    exact hRθ.symm.trans hSθ
  have haee : (fun θ : ℝ => extend R θ) =ᵐ[volume.restrict (Icc 0 Real.pi)]
      (fun θ : ℝ => extend S θ) := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    simpa only [angleMeasure, extend_coe] using hae
  have hclosed := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt Real.pi_pos) haee
    (extend R).continuous.continuousOn (extend S).continuous.continuousOn
  ext θ
  simpa only [extend_coe] using hclosed θ.property

@[simp]
theorem embed_eq_iff (R S : Profile) : embed R = embed S ↔ R = S :=
  embed_injective.eq_iff

/-- Every nonzero continuous profile remains nonzero in `L²`. -/
theorem embed_ne_zero {R : Profile} (hR : R ≠ 0) : embed R ≠ 0 := by
  intro hz
  apply hR
  apply embed_injective
  simpa using hz

/-- Positive radial profiles give nonzero `L²` vectors without any extra
assumption about a.e. representatives. -/
theorem embed_ne_zero_of_positive {R : Profile} (hR : ∀ θ, 0 < R θ) : embed R ≠ 0 := by
  apply embed_ne_zero
  intro hz
  have h := hR ⟨0, le_rfl, Real.pi_pos.le⟩
  simp [hz] at h

/-- The concrete `L²` inner product is the angular integral of profile products. -/
theorem inner_embed (R S : Profile) :
    inner (𝕜 := ℝ) (embed R) (embed S) =
      ∫ θ in Ioo (0 : ℝ) Real.pi, extend R θ * extend S θ := by
  have h := ContinuousMap.inner_toLp angleMeasure R S
  change inner (𝕜 := ℝ) (embed R) (embed S) = _ at h
  rw [h]
  have hsub : (∫ θ : Angle, S θ * R θ ∂angleMeasure) =
      ∫ θ in Icc (0 : ℝ) Real.pi, extend R θ * extend S θ := by
    rw [← integral_subtype_comap measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with θ
    simp [angleMeasure, mul_comm]
  simpa only [RCLike.conj_to_real] using hsub.trans integral_Icc_eq_integral_Ioo

/-- Exact squared `L²` norm, with the same open-interval integral as (3.5). -/
theorem norm_sq_embed (R : Profile) :
    ‖embed R‖ ^ 2 = ∫ θ in Ioo (0 : ℝ) Real.pi, (extend R θ) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_embed]
  simp only [pow_two]

/-- The original radial-area expression equals the concrete Hilbert area. -/
theorem profileArea_embed (R : Profile) :
    profileArea (embed R) = Torsion.radialArea (extend R) := by
  rw [profileArea, norm_sq_embed]
  unfold Torsion.radialArea
  ring

/-- Equation (3.5) for the concrete `L²` embedding. -/
theorem norm_sq_eq_twice_radialArea (R : Profile) :
    ‖embed R‖ ^ 2 = 2 * Torsion.radialArea (extend R) := by
  rw [norm_sq_embed]
  unfold Torsion.radialArea
  ring

/-- The concrete angular `L²` norm. -/
def l2Norm (R : Profile) : ℝ := ‖embed R‖

/-- Normalize the actual continuous profile by its angular `L²` norm. -/
def unitProfile (R : Profile) : Profile := (l2Norm R)⁻¹ • R

@[simp]
theorem embed_unitProfile (R : Profile) : embed (unitProfile R) = Torsion.Stability.normalize (embed R) := by
  simp [unitProfile, l2Norm, Torsion.Stability.normalize]

/-- The norm of the difference is exactly the angular square integral. -/
theorem norm_sq_sub_embed (R S : Profile) :
    ‖embed R - embed S‖ ^ 2 =
      ∫ θ in Ioo (0 : ℝ) Real.pi, (extend R θ - extend S θ) ^ 2 := by
  rw [← map_sub, norm_sq_embed]
  rfl

/-- The normalized-profile distance in (8.1) is an actual angular integral. -/
theorem norm_sq_normalized_sub_embed (R S : Profile) :
    ‖Torsion.Stability.normalize (embed R) - Torsion.Stability.normalize (embed S)‖ ^ 2 =
      ∫ θ in Ioo (0 : ℝ) Real.pi,
        (extend R θ / l2Norm R - extend S θ / l2Norm S) ^ 2 := by
  rw [← embed_unitProfile, ← embed_unitProfile, norm_sq_sub_embed]
  congr 1
  ext θ
  simp [unitProfile, extend, ContinuousMap.IccExtend, Set.IccExtend,
    div_eq_mul_inv, mul_comm]

/-- Positive continuous profiles have strictly positive radial area. -/
theorem radialArea_pos {R : Profile} (hR : ∀ θ, 0 < R θ) :
    0 < Torsion.radialArea (extend R) := by
  rw [← profileArea_embed]
  exact Torsion.Calibration.profileArea_pos (embed_ne_zero_of_positive hR)

/-- The normalized actual marked flux, using the angular area integral. -/
def fluxRatio (Q : Profile → ℝ) (R : Profile) : ℝ :=
  Q R / Real.sqrt (Torsion.radialArea (extend R))

/-- A flux on continuous profiles can be extended to `L²` because the
embedding is injective. Values away from continuous profiles are irrelevant. -/
private def liftFlux (Q : Profile → ℝ) : ProfileL2 → ℝ := Function.extend embed Q 0

@[simp]
private theorem liftFlux_embed (Q : Profile → ℝ) (R : Profile) :
    liftFlux Q (embed R) = Q R :=
  embed_injective.extend_apply Q 0 R

private theorem liftFlux_ratio (Q : Profile → ℝ) (R : Profile) :
    Torsion.RadialStability.normalizedFlux (liftFlux Q) (embed R) = fluxRatio Q R := by
  simp [Torsion.RadialStability.normalizedFlux, fluxRatio, profileArea_embed]

private theorem liftFlux_euler {Q : Profile → ℝ} {R₀ : Profile} {lam : ℝ}
    (heuler : Q R₀ = 2 * lam * Torsion.radialArea (extend R₀)) :
    liftFlux Q (embed R₀) = lam * ‖embed R₀‖ ^ 2 := by
  rw [liftFlux_embed, norm_sq_eq_twice_radialArea, heuler]
  ring

/-- The full continuum form of (8.1), conditional only on the stated
stationary marked-flux calibration and reference Euler identity. All norms
and distances here have been identified with actual angular integrals. -/
theorem continuous_quadratic_deficit {Q : Profile → ℝ} {R₀ R : Profile} {lam : ℝ}
    (hR₀ : ∀ θ, 0 < R₀ θ) (hR : ∀ θ, 0 < R θ)
    (hcal : Q R ≤ lam * ∫ θ in Ioo (0 : ℝ) Real.pi, extend R₀ θ * extend R θ)
    (heuler : Q R₀ = 2 * lam * Torsion.radialArea (extend R₀)) :
    fluxRatio Q R₀ / 2 *
        (∫ θ in Ioo (0 : ℝ) Real.pi,
          (extend R θ / l2Norm R - extend R₀ θ / l2Norm R₀) ^ 2) ≤
      fluxRatio Q R₀ - fluxRatio Q R := by
  have hc : liftFlux Q (embed R) ≤ lam * inner (𝕜 := ℝ) (embed R₀) (embed R) := by
    simpa only [liftFlux_embed, inner_embed] using hcal
  have h := Torsion.RadialStability.quadratic_deficit
    (embed_ne_zero_of_positive hR₀) (embed_ne_zero_of_positive hR) hc (liftFlux_euler heuler)
  simpa only [liftFlux_ratio, norm_sq_normalized_sub_embed] using h

/-- Equality at the optimal normalized marked flux determines the continuous
profile up to a positive scalar, including both endpoints. -/
theorem continuous_rigidity {Q : Profile → ℝ} {R₀ R : Profile} {lam : ℝ}
    (hR₀ : ∀ θ, 0 < R₀ θ) (hR : ∀ θ, 0 < R θ) (hlam : 0 < lam)
    (hcal : Q R ≤ lam * ∫ θ in Ioo (0 : ℝ) Real.pi, extend R₀ θ * extend R θ)
    (heuler : Q R₀ = 2 * lam * Torsion.radialArea (extend R₀))
    (hoptimal : fluxRatio Q R = fluxRatio Q R₀) :
    ∃ t : ℝ, 0 < t ∧ R = t • R₀ := by
  have hc : liftFlux Q (embed R) ≤ lam * inner (𝕜 := ℝ) (embed R₀) (embed R) := by
    simpa only [liftFlux_embed, inner_embed] using hcal
  have hopt : Torsion.RadialStability.normalizedFlux (liftFlux Q) (embed R) =
      Torsion.RadialStability.normalizedFlux (liftFlux Q) (embed R₀) := by
    simpa only [liftFlux_ratio] using hoptimal
  obtain ⟨t, ht, heq⟩ := Torsion.RadialStability.rigidity
    (embed_ne_zero_of_positive hR₀) (embed_ne_zero_of_positive hR) hlam hc
    (liftFlux_euler heuler) hopt
  refine ⟨t, ht, embed_injective ?_⟩
  simpa only [map_smul] using heq

/-- The continuum area-one inequality (8.2). Its squared distance is the
actual integral of `(R - R₀)²` on `(0, π)`. -/
theorem continuous_area_one_deficit {Q : Profile → ℝ} {R₀ R : Profile} {lam : ℝ}
    (hA₀ : Torsion.radialArea (extend R₀) = 1)
    (hA : Torsion.radialArea (extend R) = 1)
    (hcal : Q R ≤ lam * ∫ θ in Ioo (0 : ℝ) Real.pi, extend R₀ θ * extend R θ)
    (heuler : Q R₀ = 2 * lam * Torsion.radialArea (extend R₀)) :
    Q R₀ / 4 * (∫ θ in Ioo (0 : ℝ) Real.pi, (extend R θ - extend R₀ θ) ^ 2) ≤
      Q R₀ - Q R := by
  have hc : liftFlux Q (embed R) ≤ lam * inner (𝕜 := ℝ) (embed R₀) (embed R) := by
    simpa only [liftFlux_embed, inner_embed] using hcal
  have h := Torsion.RadialStability.area_one_deficit
    (show profileArea (embed R₀) = 1 by simpa only [profileArea_embed] using hA₀)
    (show profileArea (embed R) = 1 by simpa only [profileArea_embed] using hA)
    hc (liftFlux_euler heuler)
  simpa only [liftFlux_embed, norm_sq_sub_embed] using h

/-- At area one, equality determines the continuous profile itself everywhere. -/
theorem continuous_area_one_rigidity {Q : Profile → ℝ} {R₀ R : Profile} {lam : ℝ}
    (hA₀ : Torsion.radialArea (extend R₀) = 1)
    (hA : Torsion.radialArea (extend R) = 1) (hlam : 0 < lam)
    (hcal : Q R ≤ lam * ∫ θ in Ioo (0 : ℝ) Real.pi, extend R₀ θ * extend R θ)
    (heuler : Q R₀ = 2 * lam * Torsion.radialArea (extend R₀)) (hoptimal : Q R = Q R₀) :
    R = R₀ := by
  have hc : liftFlux Q (embed R) ≤ lam * inner (𝕜 := ℝ) (embed R₀) (embed R) := by
    simpa only [liftFlux_embed, inner_embed] using hcal
  apply embed_injective
  apply Torsion.RadialStability.area_one_rigidity
    (show profileArea (embed R₀) = 1 by simpa only [profileArea_embed] using hA₀)
    (show profileArea (embed R) = 1 by simpa only [profileArea_embed] using hA)
    hlam hc (liftFlux_euler heuler)
  simpa only [liftFlux_embed] using hoptimal

/-- A positive compact-interval profile gives an actual marked planar domain. -/
theorem domain_isMarked {R : Profile} (hR : ∀ θ, 0 < R θ) :
    Torsion.IsMarked (Torsion.radialDomain (extend R)) := by
  apply Torsion.RadialGeometry.radialDomain_isMarked (extend R).continuous.continuousOn
  intro θ hθ
  change 0 < extend R (⟨θ, hθ⟩ : Angle)
  rw [extend_coe]
  exact hR _

/-- The Hilbert profile area equals the genuine Euclidean measure of the
actual marked radial domain, completing the polar-area identification. -/
theorem geometric_area_eq_profileArea {R : Profile} (hR : ∀ θ, 0 < R θ) :
    (volume (Torsion.radialDomain (extend R))).toReal = profileArea (embed R) := by
  rw [profileArea_embed]
  apply Torsion.RadialGeometry.area_radialDomain (extend R).continuous.continuousOn
  intro θ hθ
  change 0 < extend R (⟨θ, hθ⟩ : Angle)
  rw [extend_coe]
  exact hR _

end Torsion.ContinuousProfiles

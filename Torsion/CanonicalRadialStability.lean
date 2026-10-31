module

public import Torsion.CanonicalHadamard
public import Torsion.RadialSymmetricDifference

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Concrete stability and rigidity for the canonical marked optimizer

The calibration and Euler identities here are proved facts for the actual
second-eigenfunction Cauchy domain, not hypotheses. The competitors are
positive continuous radial profiles with the marked point and supporting
half-plane fixed. The flux is the genuine marked weak-torsion flux.

These statements do not assert stability of the full essential-gradient
objective on arbitrary convex domains.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise symmDiff

namespace Torsion.Spectral

/-- The canonical radius has the actual area supplied by its spectral moments. -/
theorem secondRadialProfile_area :
    radialArea (ContinuousProfiles.extend secondRadialProfile) = secondMoments.area := by
  rw [← ContinuousProfiles.profileArea_embed, Calibration.profileArea,
    secondRadialProfile_norm_sq, secondMoments.area_eq]
  rfl

/-- The reference's normalized genuine marked flux is the exact spectral constant. -/
theorem secondRadialProfile_fluxRatio :
    ContinuousProfiles.fluxRatio
      (fun R => torsionFlux (radialDomain (ContinuousProfiles.extend R)))
      secondRadialProfile = spectralConstant secondEigenvalue secondEigenfunction := by
  unfold ContinuousProfiles.fluxRatio
  dsimp only
  rw [secondRadialProfile_domain, secondCauchyDomain_flux, secondRadialProfile_area]
  exact secondMoments.normalized_flux_eq

/-- The proved calibration in the angular-integral form used by the deficit lemmas. -/
theorem second_radial_calibration_integral (R : ContinuousProfiles.Profile)
    (hR : ∀ θ, 0 < R θ) :
    torsionFlux (radialDomain (ContinuousProfiles.extend R)) ≤
      secondMoments.stationarity * ∫ θ in Ioo (0 : ℝ) Real.pi,
        ContinuousProfiles.extend secondRadialProfile θ * ContinuousProfiles.extend R θ := by
  simpa only [secondCalibrationDensity, real_inner_smul_left,
    ContinuousProfiles.inner_embed] using second_radial_calibration R hR

/-- The actual Euler identity, with its area normalization made explicit. -/
theorem secondRadialProfile_area_euler :
    torsionFlux (radialDomain (ContinuousProfiles.extend secondRadialProfile)) =
      2 * secondMoments.stationarity *
        radialArea (ContinuousProfiles.extend secondRadialProfile) := by
  rw [secondRadialProfile_euler, ContinuousProfiles.norm_sq_eq_twice_radialArea]
  ring

/-- The normalized angular deficit for the actual canonical spectral optimizer.
Only positivity and continuity of the competing radius remain as hypotheses. -/
theorem second_radial_normalized_deficit (R : ContinuousProfiles.Profile)
    (hR : ∀ θ, 0 < R θ) :
    spectralConstant secondEigenvalue secondEigenfunction / 2 *
        (∫ θ in Ioo (0 : ℝ) Real.pi,
          (ContinuousProfiles.extend R θ / ContinuousProfiles.l2Norm R -
            ContinuousProfiles.extend secondRadialProfile θ /
              ContinuousProfiles.l2Norm secondRadialProfile) ^ 2) ≤
      spectralConstant secondEigenvalue secondEigenfunction -
        torsionFlux (radialDomain (ContinuousProfiles.extend R)) /
          Real.sqrt (radialArea (ContinuousProfiles.extend R)) := by
  have h := ContinuousProfiles.continuous_quadratic_deficit
    (Q := fun R => torsionFlux (radialDomain (ContinuousProfiles.extend R)))
    (lam := secondMoments.stationarity)
    secondRadialProfile_pos hR (second_radial_calibration_integral R hR)
    secondRadialProfile_area_euler
  rw [secondRadialProfile_fluxRatio] at h
  exact h

/-- Equality in normalized marked flux forces positive proportionality to the
canonical radius, pointwise on the entire closed angular interval. -/
theorem second_radial_rigidity (R : ContinuousProfiles.Profile)
    (hR : ∀ θ, 0 < R θ)
    (hoptimal : torsionFlux (radialDomain (ContinuousProfiles.extend R)) /
      Real.sqrt (radialArea (ContinuousProfiles.extend R)) =
        spectralConstant secondEigenvalue secondEigenfunction) :
    ∃ t : ℝ, 0 < t ∧ R = t • secondRadialProfile := by
  apply ContinuousProfiles.continuous_rigidity secondRadialProfile_pos hR
    (Q := fun R => torsionFlux (radialDomain (ContinuousProfiles.extend R)))
    secondMoments.stationarity_pos (second_radial_calibration_integral R hR)
    secondRadialProfile_area_euler
  exact hoptimal.trans secondRadialProfile_fluxRatio.symm

/-- The actual canonical radial profile rescaled to planar area one. -/
def secondAreaOneRadialProfile : ContinuousProfiles.Profile :=
  (Real.sqrt secondMoments.area)⁻¹ • secondRadialProfile

theorem secondAreaOneRadialProfile_pos (θ : ContinuousProfiles.Angle) :
    0 < secondAreaOneRadialProfile θ := by
  change 0 < (Real.sqrt secondMoments.area)⁻¹ * secondRadialProfile θ
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr secondMoments.area_pos))
    (secondRadialProfile_pos θ)

theorem secondAreaOneRadialProfile_norm_sq :
    ‖ContinuousProfiles.embed secondAreaOneRadialProfile‖ ^ 2 = 2 := by
  have hn : ‖ContinuousProfiles.embed secondRadialProfile‖ ^ 2 =
      2 * secondMoments.area := by
    rw [ContinuousProfiles.norm_sq_eq_twice_radialArea, secondRadialProfile_area]
  rw [secondAreaOneRadialProfile, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr secondMoments.area_pos)), mul_pow,
    inv_pow, hn, Real.sq_sqrt secondMoments.area_pos.le]
  field_simp [secondMoments.area_pos.ne']

theorem secondAreaOneRadialProfile_area :
    radialArea (ContinuousProfiles.extend secondAreaOneRadialProfile) = 1 := by
  rw [← ContinuousProfiles.profileArea_embed, Calibration.profileArea,
    secondAreaOneRadialProfile_norm_sq]
  norm_num

private theorem extend_smul_profile (t : ℝ) (R : ContinuousProfiles.Profile) :
    (ContinuousProfiles.extend (t • R) : ℝ → ℝ) =
      t • (ContinuousProfiles.extend R : ℝ → ℝ) := by
  ext θ
  simp [ContinuousProfiles.extend, ContinuousMap.IccExtend, Set.IccExtend]

/-- The normalized radius describes the original normalized spectral Cauchy image. -/
theorem secondAreaOneRadialProfile_domain :
    radialDomain (ContinuousProfiles.extend secondAreaOneRadialProfile) =
      normalizedImage secondEigenvalue secondEigenfunction := by
  have hs : 0 < (Real.sqrt secondMoments.area)⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr secondMoments.area_pos)
  rw [secondAreaOneRadialProfile, extend_smul_profile,
    RadialFluxConcavity.radialDomain_smul _ _ hs, secondRadialProfile_domain,
    secondCauchyDomain_carrier]
  have harea : secondEigenvalue * squareMass secondEigenfunction / 2 =
      secondMoments.area := secondMoments.area_eq.symm
  unfold normalizedImage
  rw [harea]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, by simp [Complex.real_smul]⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, by simp [Complex.real_smul]⟩

/-- The area-one reference attains the exact constant in genuine marked flux. -/
theorem secondAreaOneRadialProfile_flux :
    torsionFlux (radialDomain (ContinuousProfiles.extend secondAreaOneRadialProfile)) =
      spectralConstant secondEigenvalue secondEigenfunction := by
  have hs : 0 < (Real.sqrt secondMoments.area)⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr secondMoments.area_pos)
  rw [secondAreaOneRadialProfile, extend_smul_profile,
    RadialFluxConcavity.radialDomain_smul _ _ hs,
    torsionFlux_dilate (ContinuousProfiles.domain_isMarked secondRadialProfile_pos) _ hs,
    secondRadialProfile_domain, secondCauchyDomain_flux]
  change (Real.sqrt secondMoments.area)⁻¹ * secondMoments.flux = secondMoments.sharpConstant
  simpa only [div_eq_mul_inv, mul_comm] using secondMoments.normalized_flux_eq

/-- The normalization is for genuine planar Lebesgue area. -/
theorem secondAreaOneRadialProfile_geometric_area :
    (volume (radialDomain (ContinuousProfiles.extend secondAreaOneRadialProfile))).toReal = 1 := by
  rw [ContinuousProfiles.geometric_area_eq_profileArea secondAreaOneRadialProfile_pos,
    ContinuousProfiles.profileArea_embed, secondAreaOneRadialProfile_area]

/-- The constructed calibration density expressed in area-one coordinates. -/
theorem secondCalibrationDensity_area_one :
    secondCalibrationDensity =
      (spectralConstant secondEigenvalue secondEigenfunction / 2) •
        ContinuousProfiles.embed secondAreaOneRadialProfile := by
  rw [secondCalibrationDensity, secondAreaOneRadialProfile, map_smul, smul_smul]
  congr 1
  change secondMoments.stationarity =
    (secondMoments.sharpConstant / 2) * (Real.sqrt secondMoments.area)⁻¹
  rw [← secondMoments.calibration_constant_eq]
  have hs : Real.sqrt secondMoments.area ≠ 0 :=
    (Real.sqrt_pos.mpr secondMoments.area_pos).ne'
  field_simp [hs]

/-- The concrete area-one deficit, in the genuine angular Hilbert norm. -/
theorem second_radial_area_one_deficit_norm (R : ContinuousProfiles.Profile)
    (hR : ∀ θ, 0 < R θ)
    (hA : radialArea (ContinuousProfiles.extend R) = 1) :
    spectralConstant secondEigenvalue secondEigenfunction / 4 *
        ‖ContinuousProfiles.embed R - ContinuousProfiles.embed secondAreaOneRadialProfile‖ ^ 2 ≤
      spectralConstant secondEigenvalue secondEigenfunction -
        torsionFlux (radialDomain (ContinuousProfiles.extend R)) := by
  have hn : ‖ContinuousProfiles.embed R‖ ^ 2 = 2 := by
    rw [ContinuousProfiles.norm_sq_eq_twice_radialArea, hA, mul_one]
  apply Stability.area_one_quadratic_deficit _ _ hn secondAreaOneRadialProfile_norm_sq
  have hc := second_radial_calibration R hR
  rw [secondCalibrationDensity_area_one, real_inner_smul_left] at hc
  calc
    _ ≤ _ := hc
    _ = _ := by rw [real_inner_comm]

/-- The area-one deficit written as the physical radius-square integral. -/
theorem second_radial_area_one_deficit (R : ContinuousProfiles.Profile)
    (hR : ∀ θ, 0 < R θ)
    (hA : radialArea (ContinuousProfiles.extend R) = 1) :
    spectralConstant secondEigenvalue secondEigenfunction / 4 *
        (∫ θ in Ioo (0 : ℝ) Real.pi,
          (ContinuousProfiles.extend R θ -
            ContinuousProfiles.extend secondAreaOneRadialProfile θ) ^ 2) ≤
      spectralConstant secondEigenvalue secondEigenfunction -
        torsionFlux (radialDomain (ContinuousProfiles.extend R)) := by
  rw [← ContinuousProfiles.norm_sq_sub_embed]
  exact second_radial_area_one_deficit_norm R hR hA

/-- At area one a marked maximizer has exactly the canonical continuous radius. -/
theorem second_radial_area_one_rigidity (R : ContinuousProfiles.Profile)
    (hR : ∀ θ, 0 < R θ)
    (hA : radialArea (ContinuousProfiles.extend R) = 1)
    (hoptimal : torsionFlux (radialDomain (ContinuousProfiles.extend R)) =
      spectralConstant secondEigenvalue secondEigenfunction) :
    R = secondAreaOneRadialProfile := by
  have hd := second_radial_area_one_deficit_norm R hR hA
  rw [hoptimal, sub_self] at hd
  have hc : 0 < spectralConstant secondEigenvalue secondEigenfunction / 4 :=
    div_pos secondMoments.sharpConstant_pos (by norm_num)
  have hle := nonpos_of_mul_nonpos_right hd hc
  have hz : ‖ContinuousProfiles.embed R -
      ContinuousProfiles.embed secondAreaOneRadialProfile‖ ^ 2 = 0 :=
    le_antisymm hle (sq_nonneg _)
  apply ContinuousProfiles.embed_injective
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- Exact equality classification within the area-one marked radial class. -/
theorem second_radial_area_one_equality_iff (R : ContinuousProfiles.Profile)
    (hR : ∀ θ, 0 < R θ)
    (hA : radialArea (ContinuousProfiles.extend R) = 1) :
    torsionFlux (radialDomain (ContinuousProfiles.extend R)) =
        spectralConstant secondEigenvalue secondEigenfunction ↔
      R = secondAreaOneRadialProfile := by
  constructor
  · exact second_radial_area_one_rigidity R hR hA
  · intro h
    rw [h]
    exact secondAreaOneRadialProfile_flux

/-- The concrete geometric deficit controls the genuine planar symmetric
difference from the normalized spectral Cauchy image, with the mark fixed. -/
theorem second_radial_area_one_symmDiff_deficit (R : ContinuousProfiles.Profile)
    (hR : ∀ θ, 0 < R θ)
    (hA : radialArea (ContinuousProfiles.extend R) = 1) :
    spectralConstant secondEigenvalue secondEigenfunction / 8 *
        (volume (radialDomain (ContinuousProfiles.extend R) ∆
          normalizedImage secondEigenvalue secondEigenfunction)).toReal ^ 2 ≤
      spectralConstant secondEigenvalue secondEigenfunction -
        torsionFlux (radialDomain (ContinuousProfiles.extend R)) := by
  have hg := ContinuousProfiles.area_one_symmDiff_sq_le hR
    secondAreaOneRadialProfile_pos hA secondAreaOneRadialProfile_area
  rw [secondAreaOneRadialProfile_domain] at hg
  have hc : 0 ≤ spectralConstant secondEigenvalue secondEigenfunction / 8 :=
    div_nonneg secondMoments.sharpConstant_pos.le (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hg hc
  have hd := second_radial_area_one_deficit_norm R hR hA
  nlinarith

/-- The same geometric deficit with the hypothesis stated directly using
planar Lebesgue area, rather than the equivalent angular integral. -/
theorem second_marked_area_one_symmDiff_deficit (R : ContinuousProfiles.Profile)
    (hR : ∀ θ, 0 < R θ)
    (hA : (volume (radialDomain (ContinuousProfiles.extend R))).toReal = 1) :
    spectralConstant secondEigenvalue secondEigenfunction / 8 *
        (volume (radialDomain (ContinuousProfiles.extend R) ∆
          normalizedImage secondEigenvalue secondEigenfunction)).toReal ^ 2 ≤
      spectralConstant secondEigenvalue secondEigenfunction -
        torsionFlux (radialDomain (ContinuousProfiles.extend R)) := by
  apply second_radial_area_one_symmDiff_deficit R hR
  rwa [ContinuousProfiles.geometric_area_eq_profileArea hR,
    ContinuousProfiles.profileArea_embed] at hA

/-- Equality for an area-one marked radial domain identifies its actual set,
not only an almost-everywhere representative of its radius. -/
theorem second_marked_area_one_domain_rigidity (R : ContinuousProfiles.Profile)
    (hR : ∀ θ, 0 < R θ)
    (hA : (volume (radialDomain (ContinuousProfiles.extend R))).toReal = 1)
    (hoptimal : torsionFlux (radialDomain (ContinuousProfiles.extend R)) =
      spectralConstant secondEigenvalue secondEigenfunction) :
    radialDomain (ContinuousProfiles.extend R) =
      normalizedImage secondEigenvalue secondEigenfunction := by
  have harea : radialArea (ContinuousProfiles.extend R) = 1 := by
    rwa [ContinuousProfiles.geometric_area_eq_profileArea hR,
      ContinuousProfiles.profileArea_embed] at hA
  rw [second_radial_area_one_rigidity R hR harea hoptimal]
  exact secondAreaOneRadialProfile_domain

end Torsion.Spectral

import Torsion.CanonicalSpectralCandidate
import Torsion.RadialCalibrationSmooth

/-!
# Canonical radial calibration from the localized shape derivative

The second spectral reference, its angular density and Euler identity are
actual constructed objects. The endpoint approximation theorem therefore
reduces calibration for every positive continuous radial competitor to the
one displayed local Hadamard derivative. Neither that derivative nor the
extension to the essential gradient norm of arbitrary convex domains is
asserted as proved here.

The `_of_local_derivative` versions below use continuous endpoint-preserving
perturbations. That premise is stronger than a smooth compactly supported
Hadamard formula; it is retained as a reusable intermediate interface.
The `_of_smooth_local_derivative` versions use only the source-compatible
smooth compactly supported perturbations, with all approximation proved.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion.Spectral

theorem secondRadialProfile_extend_positive :
    (ContinuousProfiles.extend secondRadialProfile : ℝ → ℝ) ∈
      RadialFluxConcavity.positiveContinuousProfiles := by
  refine ⟨(ContinuousProfiles.extend secondRadialProfile).continuous.continuousOn, ?_⟩
  intro θ hθ
  rw [show ContinuousProfiles.extend secondRadialProfile θ = secondRadialProfile ⟨θ, hθ⟩ from
    ContinuousProfiles.extend_coe secondRadialProfile ⟨θ, hθ⟩]
  exact secondRadialProfile_pos _

/-- The actual Euler identity in precisely the raw angular integral
normalization needed by the endpoint calibration theorem. -/
theorem secondRadialProfile_integral_euler :
    torsionFlux (radialDomain (ContinuousProfiles.extend secondRadialProfile)) =
      ∫ θ in Ioo (0 : ℝ) Real.pi,
        (secondMoments.stationarity * ContinuousProfiles.extend secondRadialProfile θ) *
          ContinuousProfiles.extend secondRadialProfile θ := by
  rw [secondRadialProfile_euler, ContinuousProfiles.norm_sq_embed]
  simp_rw [pow_two, mul_assoc]
  exact (integral_const_mul _ _).symm

/-- Endpoint limits, the actual reference compatibility, and the supporting
inequality are all discharged, conditional only on the local right shape
derivative at the actual canonical domain. -/
theorem second_radial_calibration_of_local_derivative
    (hlocal : ∀ S ∈ RadialFluxConcavity.positiveContinuousProfiles,
      (∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ Icc 0 Real.pi,
        (θ ≤ ε ∨ Real.pi - ε ≤ θ) →
          S θ = ContinuousProfiles.extend secondRadialProfile θ) →
      HasDerivWithinAt (fun t : ℝ => torsionFlux (radialDomain
        (AffineMap.lineMap (ContinuousProfiles.extend secondRadialProfile : ℝ → ℝ) S t)))
        (∫ θ in Ioo 0 Real.pi,
          (secondMoments.stationarity * ContinuousProfiles.extend secondRadialProfile θ) *
            (S θ - ContinuousProfiles.extend secondRadialProfile θ)) (Ioi 0) 0)
    (R : ContinuousProfiles.Profile) (hR : ∀ θ, 0 < R θ) :
    torsionFlux (radialDomain (ContinuousProfiles.extend R)) ≤
      inner (𝕜 := ℝ) secondCalibrationDensity (ContinuousProfiles.embed R) := by
  have hRp : (ContinuousProfiles.extend R : ℝ → ℝ) ∈
      RadialFluxConcavity.positiveContinuousProfiles := by
    refine ⟨(ContinuousProfiles.extend R).continuous.continuousOn, ?_⟩
    intro θ hθ
    rw [show ContinuousProfiles.extend R θ = R ⟨θ, hθ⟩ from
      ContinuousProfiles.extend_coe R ⟨θ, hθ⟩]
    exact hR _
  have h := RadialCalibration.calibration_of_local_derivative
    secondRadialProfile_extend_positive hRp
    ((continuous_const.mul (ContinuousProfiles.extend secondRadialProfile).continuous).continuousOn)
    secondRadialProfile_integral_euler hlocal
  rw [secondCalibrationDensity, real_inner_smul_left, ContinuousProfiles.inner_embed]
  simpa only [mul_assoc, integral_const_mul] using h

/-- Cauchy--Schwarz with the exact constructed density gives the sharp
spectral marked-flux bound for the whole positive continuous radial class,
once the localized Hadamard formula is proved. -/
theorem second_radial_bound_of_local_derivative
    (hlocal : ∀ S ∈ RadialFluxConcavity.positiveContinuousProfiles,
      (∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ Icc 0 Real.pi,
        (θ ≤ ε ∨ Real.pi - ε ≤ θ) →
          S θ = ContinuousProfiles.extend secondRadialProfile θ) →
      HasDerivWithinAt (fun t : ℝ => torsionFlux (radialDomain
        (AffineMap.lineMap (ContinuousProfiles.extend secondRadialProfile : ℝ → ℝ) S t)))
        (∫ θ in Ioo 0 Real.pi,
          (secondMoments.stationarity * ContinuousProfiles.extend secondRadialProfile θ) *
            (S θ - ContinuousProfiles.extend secondRadialProfile θ)) (Ioi 0) 0)
    (R : ContinuousProfiles.Profile) (hR : ∀ θ, 0 < R θ) :
    torsionFlux (radialDomain (ContinuousProfiles.extend R)) ≤
      spectralConstant secondEigenvalue secondEigenfunction *
        Real.sqrt (radialArea (ContinuousProfiles.extend R)) := by
  have hnorm := Calibration.norm_eq_sqrt_two_mul_sqrt_profileArea (ContinuousProfiles.embed R)
  rw [ContinuousProfiles.profileArea_embed] at hnorm
  calc
    _ ≤ inner (𝕜 := ℝ) secondCalibrationDensity (ContinuousProfiles.embed R) :=
      second_radial_calibration_of_local_derivative hlocal R hR
    _ ≤ ‖secondCalibrationDensity‖ * ‖ContinuousProfiles.embed R‖ := real_inner_le_norm _ _
    _ = (Real.sqrt 2 * ‖secondCalibrationDensity‖) *
        Real.sqrt (radialArea (ContinuousProfiles.extend R)) := by rw [hnorm]; ring
    _ = _ := by rw [secondCalibrationDensity_constant]

/-- The primary source-compatible canonical supporting theorem: only the
localized Hadamard formula for genuine smooth, compactly supported angular
perturbations remains. The complete continuous competitor class and all
endpoint and smooth-approximation passages are conclusions. -/
theorem second_radial_calibration_of_smooth_local_derivative
    (hlocal : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo 0 Real.pi →
      (fun θ => ContinuousProfiles.extend secondRadialProfile θ + f θ) ∈
        RadialFluxConcavity.positiveContinuousProfiles →
      HasDerivWithinAt (fun t : ℝ => torsionFlux (radialDomain
        (fun θ => ContinuousProfiles.extend secondRadialProfile θ + t * f θ)))
        (∫ θ in Ioo 0 Real.pi,
          (secondMoments.stationarity * ContinuousProfiles.extend secondRadialProfile θ) * f θ)
        (Ioi 0) 0)
    (R : ContinuousProfiles.Profile) (hR : ∀ θ, 0 < R θ) :
    torsionFlux (radialDomain (ContinuousProfiles.extend R)) ≤
      inner (𝕜 := ℝ) secondCalibrationDensity (ContinuousProfiles.embed R) := by
  have hRp : (ContinuousProfiles.extend R : ℝ → ℝ) ∈
      RadialFluxConcavity.positiveContinuousProfiles := by
    refine ⟨(ContinuousProfiles.extend R).continuous.continuousOn, ?_⟩
    intro θ hθ
    rw [show ContinuousProfiles.extend R θ = R ⟨θ, hθ⟩ from
      ContinuousProfiles.extend_coe R ⟨θ, hθ⟩]
    exact hR _
  have h := RadialCalibration.calibration_of_smooth_local_derivative
    secondRadialProfile_extend_positive hRp
    ((continuous_const.mul (ContinuousProfiles.extend secondRadialProfile).continuous).continuousOn)
    secondRadialProfile_integral_euler hlocal
  rw [secondCalibrationDensity, real_inner_smul_left, ContinuousProfiles.inner_embed]
  simpa only [mul_assoc, integral_const_mul] using h

/-- The sharp spectral radial bound with exactly the smooth local
Hadamard premise used by the manuscript. This is a marked-flux statement;
the universal convex-domain essential-gradient bound remains separate. -/
theorem second_radial_bound_of_smooth_local_derivative
    (hlocal : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo 0 Real.pi →
      (fun θ => ContinuousProfiles.extend secondRadialProfile θ + f θ) ∈
        RadialFluxConcavity.positiveContinuousProfiles →
      HasDerivWithinAt (fun t : ℝ => torsionFlux (radialDomain
        (fun θ => ContinuousProfiles.extend secondRadialProfile θ + t * f θ)))
        (∫ θ in Ioo 0 Real.pi,
          (secondMoments.stationarity * ContinuousProfiles.extend secondRadialProfile θ) * f θ)
        (Ioi 0) 0)
    (R : ContinuousProfiles.Profile) (hR : ∀ θ, 0 < R θ) :
    torsionFlux (radialDomain (ContinuousProfiles.extend R)) ≤
      spectralConstant secondEigenvalue secondEigenfunction *
        Real.sqrt (radialArea (ContinuousProfiles.extend R)) := by
  have hnorm := Calibration.norm_eq_sqrt_two_mul_sqrt_profileArea (ContinuousProfiles.embed R)
  rw [ContinuousProfiles.profileArea_embed] at hnorm
  calc
    _ ≤ inner (𝕜 := ℝ) secondCalibrationDensity (ContinuousProfiles.embed R) :=
      second_radial_calibration_of_smooth_local_derivative hlocal R hR
    _ ≤ ‖secondCalibrationDensity‖ * ‖ContinuousProfiles.embed R‖ := real_inner_le_norm _ _
    _ = (Real.sqrt 2 * ‖secondCalibrationDensity‖) *
        Real.sqrt (radialArea (ContinuousProfiles.extend R)) := by rw [hnorm]; ring
    _ = _ := by rw [secondCalibrationDensity_constant]

end Torsion.Spectral

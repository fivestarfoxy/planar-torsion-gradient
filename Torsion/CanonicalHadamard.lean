module

public import Torsion.CauchyRadialHadamard
public import Torsion.CanonicalRadialCalibration

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Localized Hadamard formula and the actual canonical radial calibration

The actual second spectral profile supplies every input of the localized
shape theorem. The existing endpoint approximation and concavity results
then give the sharp marked-flux bound for all positive continuous radial
competitors. The universal interior-gradient comparison is separate.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion.Spectral

/-- The localized marked Hadamard formula for the constructed canonical
second spectral domain, with its original angular density. -/
theorem second_localized_hadamard (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ Ioo 0 Real.pi) :
    HasDerivAt (fun t : ℝ => torsionFlux (radialDomain
      (fun θ => ContinuousProfiles.extend secondRadialProfile θ + t * f θ)))
      (∫ θ in Ioo 0 Real.pi,
        (secondMoments.stationarity * ContinuousProfiles.extend secondRadialProfile θ) * f θ) 0 := by
  have h := cauchy_radial_torsionFlux_hasDerivAt
    secondEigenfunction_isRestrictedEigenfunction secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
    secondHolderConstant_spec (by norm_num) (by norm_num) secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation
    secondEigenfunction_concaveOn_Ioo secondEigenfunction_differentiableAt_positive f hf hfc hfU
  have hcoef : secondMoments.stationarity =
      1 / (2 * secondEigenvalue * mass secondEigenfunction) := rfl
  have heq : (∫ θ in Ioo 0 Real.pi,
      (secondMoments.stationarity * ContinuousProfiles.extend secondRadialProfile θ) * f θ) =
      (1 / (2 * secondEigenvalue * mass secondEigenfunction)) *
        ∫ θ in Ioo 0 Real.pi, ContinuousProfiles.extend secondRadialProfile θ * f θ := by
    rw [hcoef, ← integral_const_mul]
    congr 1
    ext θ
    ring
  rw [heq]
  exact h

/-- The actual canonical density supports every positive continuous radial
competitor. The local shape derivative and all endpoint limits are proved. -/
theorem second_radial_calibration (R : ContinuousProfiles.Profile) (hR : ∀ θ, 0 < R θ) :
    torsionFlux (radialDomain (ContinuousProfiles.extend R)) ≤
      inner (𝕜 := ℝ) secondCalibrationDensity (ContinuousProfiles.embed R) := by
  apply second_radial_calibration_of_smooth_local_derivative
  · intro f hf hfc hfU _
    exact (second_localized_hadamard f hf hfc hfU).hasDerivWithinAt
  · exact hR

/-- The sharp spectral marked-flux bound on the entire original positive
continuous radial class, without a local shape or endpoint premise. -/
theorem second_radial_bound (R : ContinuousProfiles.Profile) (hR : ∀ θ, 0 < R θ) :
    torsionFlux (radialDomain (ContinuousProfiles.extend R)) ≤
      spectralConstant secondEigenvalue secondEigenfunction *
        Real.sqrt (radialArea (ContinuousProfiles.extend R)) := by
  apply second_radial_bound_of_smooth_local_derivative
  · intro f hf hfc hfU _
    exact (second_localized_hadamard f hf hfc hfU).hasDerivWithinAt
  · exact hR

end Torsion.Spectral

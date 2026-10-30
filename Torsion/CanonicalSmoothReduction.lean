module

public import Torsion.CanonicalSpectralCandidate
public import Torsion.SmoothConvexReduction

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The canonical final bridge reduced to smooth competitor comparison

The smooth outer approximants and passage of actual weak-gradient bounds
are constructed. Thus proving the sharp comparison on smooth strictly
convex regular sublevels suffices for the original full admissible class.
This comparison remains a substantive explicit proof parameter.
-/

noncomputable section
open Set
open scoped ContDiff

namespace Torsion
open Spectral

theorem second_universal_of_smooth_comparison
    (hbound : ∀ (E : ConvexDomain) (F : Plane → ℝ) (c : ℝ),
      ContDiff ℝ ∞ F → StrictConvex ℝ (closure E.carrier) →
      (∀ x ∈ frontier E.carrier, fderiv ℝ F x ≠ 0) →
      E.carrier = {x | F x < c} →
      torsionTheory.G E ≤ ENNReal.ofReal
        (spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt E.area)) :
    ∀ D : ConvexDomain, torsionTheory.G D ≤ ENNReal.ofReal
      (2 * secondMoments.stationarity * Real.sqrt secondMoments.area * Real.sqrt D.area) := by
  intro D
  have h := torsionTheory.G_area_bound_of_smooth_strictConvex
    (spectralConstant secondEigenvalue secondEigenfunction) hbound D
  have hc : 2 * secondMoments.stationarity * Real.sqrt secondMoments.area =
      spectralConstant secondEigenvalue secondEigenfunction :=
    secondMoments.calibration_constant_eq
  simpa only [hc] using h

/-- The existing final interface, still conditional on the sharp smooth
comparison, with all approximation and limit hypotheses discharged. -/
def secondSpectralBridge_of_smooth_comparison
    (hbound : ∀ (E : ConvexDomain) (F : Plane → ℝ) (c : ℝ),
      ContDiff ℝ ∞ F → StrictConvex ℝ (closure E.carrier) →
      (∀ x ∈ frontier E.carrier, fderiv ℝ F x ≠ 0) →
      E.carrier = {x | F x < c} →
      torsionTheory.G E ≤ ENNReal.ofReal
        (spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt E.area)) :
    SpectralBridge torsionTheory secondEigenvalue secondEigenfunction :=
  secondSpectralBridge_of_universal (second_universal_of_smooth_comparison hbound)

end Torsion

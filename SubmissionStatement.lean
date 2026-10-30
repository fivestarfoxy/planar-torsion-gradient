import Torsion.ProvedMain
import Torsion.RestrictedSpectralSecondProfile
import Torsion.SpectralNormalization

/-!
Concrete submission claim, stated using the original mathematical objects.
This module contains no proof of the claim and does not import the final
canonical optimization or universal-comparison modules.
-/

namespace TorsionSubmission

/-- Universal sharp bound, exact optimal value, and attainment by the actual
area-normalized second-eigenfunction Cauchy image. Uniqueness is not asserted. -/
def Claim : Prop :=
  (∀ D : Torsion.ConvexDomain,
    Torsion.torsionTheory.G D ≤ ENNReal.ofReal
      (Torsion.Spectral.spectralConstant Torsion.Spectral.secondEigenvalue
        Torsion.Spectral.secondEigenfunction * Real.sqrt D.area)) ∧
  Torsion.torsionTheory.cStar = ENNReal.ofReal
    (Torsion.Spectral.spectralConstant Torsion.Spectral.secondEigenvalue
      Torsion.Spectral.secondEigenfunction) ∧
  ∃ D : Torsion.ConvexDomain,
    D.carrier = Torsion.Spectral.normalizedImage Torsion.Spectral.secondEigenvalue
      Torsion.Spectral.secondEigenfunction ∧
    D.area = 1 ∧
    Torsion.torsionTheory.G D = ENNReal.ofReal
      (Torsion.Spectral.spectralConstant Torsion.Spectral.secondEigenvalue
        Torsion.Spectral.secondEigenfunction)

end TorsionSubmission

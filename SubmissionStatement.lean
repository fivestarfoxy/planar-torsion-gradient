module

public import Torsion.ProvedMain
public import Torsion.RestrictedSpectralSecondProfile
public import Torsion.SpectralNormalization

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
Concrete submission claim, stated using the original mathematical objects.
This module contains no proof of the claim and does not import the final
canonical optimization or universal-comparison modules.
-/

namespace TorsionSubmission

/-- Universal sharp bound, exact optimal value, and attainment by the actual
area-normalized second-eigenfunction Cauchy image. -/
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

/-- Theorem 1.2 for the original weak-gradient objective on every bounded,
nonempty open convex planar domain, with no regularity hypothesis at the mark. -/
def Classification : Prop :=
  ∀ D : Torsion.ConvexDomain,
    Torsion.torsionTheory.G D = ENNReal.ofReal
      (Torsion.Spectral.spectralConstant Torsion.Spectral.secondEigenvalue
        Torsion.Spectral.secondEigenfunction * Real.sqrt D.area) ↔
      ∃ (p : Torsion.Plane) (s : ℝ), 0 < s ∧ ∃ (U : Torsion.Plane ≃ₗᵢ[ℝ] Torsion.Plane),
        D.carrier = (fun z => p + s • U z) ''
          Torsion.Spectral.normalizedImage Torsion.Spectral.secondEigenvalue
            Torsion.Spectral.secondEigenfunction

end TorsionSubmission

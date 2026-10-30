import Torsion.CanonicalUniversal

/-!
# Unconditional exact spectral value and an actual maximizing domain

The constructed canonical second eigenfunction supplies the spectral data.
The universal weak-gradient bound supplies the last field of the original
reference certificate. The existing optimization theorem therefore applies
with no spectral, geometric, shape-variation or comparison arguments.
-/

noncomputable section
namespace Torsion
open Spectral

/-- A fully constructed instance of the original reference interface. -/
def secondReferenceCertificate : ReferenceCertificate torsionTheory secondMoments :=
  secondReferenceCertificate_of_universal second_universal

/-- A fully constructed instance of the original spectral bridge. -/
def secondSpectralBridge : SpectralBridge torsionTheory secondEigenvalue secondEigenfunction :=
  secondSpectralBridge_of_universal second_universal

/-- The exact optimal constant and attainment by the normalized actual
second-eigenfunction Cauchy image, with no explicit mathematical hypotheses. -/
theorem second_exact_value :
    torsionTheory.cStar = ENNReal.ofReal (spectralConstant secondEigenvalue secondEigenfunction) ∧
    ∃ D : ConvexDomain, D.carrier = normalizedImage secondEigenvalue secondEigenfunction ∧
      D.area = 1 ∧ torsionTheory.G D =
        ENNReal.ofReal (spectralConstant secondEigenvalue secondEigenfunction) :=
  exact_value_of_spectralBridge secondEigenvalue secondEigenfunction secondSpectralBridge

end Torsion

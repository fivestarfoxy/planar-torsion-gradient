import Torsion.RestrictedSpectralExteriorIntegrability
import Torsion.RestrictedSpectralSecondEndpointIntegrability

/-! Actual L¹ exterior forcing for the constructed second eigenfunction. -/
noncomputable section
open Set MeasureTheory

namespace Torsion.Spectral

/-- The actual exterior Cauchy residual of the selected second profile is
an ordinary L¹ function, by the proved square-root endpoint bound and
absolute Fubini for the original double-pole kernel. -/
theorem secondEigenfunction_exteriorResidualZero_integrable :
    Integrable (exteriorResidualZero secondEigenfunction) :=
  integrable_exteriorResidualZero_of_endpoint_quotient
    secondEigenfunction_continuous.aestronglyMeasurable
    secondEigenfunction_endpoint_quotient_integrable

end Torsion.Spectral

import Torsion.RestrictedSpectralEndpointIntegrability
import Torsion.RestrictedSpectralSecondEndpoint

/-! The endpoint quotient is integrable for the actual selected second eigenfunction. -/
noncomputable section
open Set MeasureTheory

namespace Torsion.Spectral

/-- The proved actual semicircle bound supplies precisely the endpoint
integrability used in the exterior forcing and global weak equation. -/
theorem secondEigenfunction_endpoint_quotient_integrable :
    IntegrableOn (fun x => |secondEigenfunction x| / (1 - |x|)) (Ioo (-1 : ℝ) 1) := by
  obtain ⟨C, hC, hb⟩ := secondEigenfunction_semicircle_bound
  exact integrableOn_abs_div_one_sub_abs_of_global_semicircle_bound
    secondEigenfunction_continuous.aestronglyMeasurable hC.le hb

end Torsion.Spectral

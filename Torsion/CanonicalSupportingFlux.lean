import Torsion.ConvexSupportingRadial
import Torsion.CanonicalHadamard

/-! # The actual canonical sharp comparison for supporting-boundary fluxes -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Torsion
open Spectral

/-- The unconditional canonical radial calibration bounds every genuine
supporting-boundary flux of every original convex domain. -/
theorem HasTorsionFlux.le_second_spectral_bound {D : ConvexDomain} {q : ℝ}
    (hq : HasTorsionFlux D.carrier q) (hzero : (0 : Plane) ∈ closure D.carrier)
    (hhalf : D.carrier ⊆ upperHalfPlane) :
    q ≤ spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt D.area :=
  hq.le_of_positive_radial_bound hzero hhalf second_radial_bound

/-- The same canonical comparison requires only an actual interior-continuous
weak solution, its inward quotient, and eventual inward normal-ray entry. -/
theorem HasMarkedFlux.le_second_spectral_bound
    {D : ConvexDomain} {u : Plane → ℝ} {g : Plane → Plane} {q : ℝ}
    (hq : HasMarkedFlux u q) (hu : IsWeakTorsion D.carrier u g)
    (huc : ContinuousOn u D.carrier) (hzero : (0 : Plane) ∈ closure D.carrier)
    (hhalf : D.carrier ⊆ upperHalfPlane)
    (hline : ∀ᶠ t : ℝ in 𝓝[>] 0, (t : ℂ) * Complex.I ∈ D.carrier) :
    q ≤ spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt D.area :=
  hq.le_of_positive_radial_bound hu huc hzero hhalf hline second_radial_bound

end Torsion

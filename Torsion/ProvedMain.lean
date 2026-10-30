import Torsion.HilbertDirichlet
import Torsion.DilationWeak
import Torsion.SpectralMain
import Torsion.SpectralNormalization

/-!
# Main theorem after constructing weak Dirichlet theory and proving scaling

The weak solution theory and physical scaling law are now proved objects,
not assumptions of these entry points. The remaining spectral/geometric
calibration bridge is still an explicit, unconstructed argument.
-/
noncomputable section
namespace Torsion

/-- Actual weak torsion theory obtained from the closed H¹₀ graph,
Poincaré inequality and Lax--Milgram theorem. -/
def torsionTheory : DirichletTheory := HilbertDirichlet.dirichletTheory

/-- Value and attainment now require no unproved Dirichlet or scaling law.
The analytic reference certificate remains to be constructed. -/
theorem exact_value_of_reference (d : Moments) (C : ReferenceCertificate torsionTheory d) :
    torsionTheory.cStar = ENNReal.ofReal d.sharpConstant ∧
    ∃ D : ConvexDomain, D.area = 1 ∧
      torsionTheory.G D = ENNReal.ofReal d.sharpConstant :=
  conditional_exact_value torsionTheory d (ScalingLaw.proved torsionTheory) C

/-- Spectral formulation with the proved base theory and scaling.
The only remaining proof parameter is the explicit spectral reference bridge. -/
theorem exact_value_of_spectralBridge (a : ℝ) (φ : ℝ → ℝ)
    (B : SpectralBridge torsionTheory a φ) :
    torsionTheory.cStar = ENNReal.ofReal (Spectral.spectralConstant a φ) ∧
    ∃ D : ConvexDomain, D.carrier = Spectral.normalizedImage a φ ∧
      D.area = 1 ∧ torsionTheory.G D = ENNReal.ofReal (Spectral.spectralConstant a φ) := by
  simpa only [Spectral.spectralConstant, Spectral.normalizedImage, Complex.ofReal_inv] using
    conditional_spectral_exact_value torsionTheory (ScalingLaw.proved torsionTheory) a φ B

end Torsion
end

module

public import Torsion.HilbertDirichlet
public import Torsion.DilationWeak
public import Torsion.SpectralMain
public import Torsion.SpectralNormalization

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Main theorem after constructing weak Dirichlet theory and proving scaling

The weak solution theory and physical scaling law are now proved objects,
not assumptions of these entry points. At this layer the spectral/geometric
calibration bridge remains an explicit argument; `CanonicalOptimization`
constructs it and supplies the unconditional endpoint.
-/
noncomputable section
namespace Torsion

/-- Actual weak torsion theory obtained from the closed H¹₀ graph,
Poincaré inequality and Lax--Milgram theorem. -/
def torsionTheory : DirichletTheory := HilbertDirichlet.dirichletTheory

/-- Value and attainment now require no unproved Dirichlet or scaling law.
The analytic reference certificate is an explicit argument here and is
constructed in `CanonicalOptimization`. -/
theorem exact_value_of_reference (d : Moments) (C : ReferenceCertificate torsionTheory d) :
    torsionTheory.cStar = ENNReal.ofReal d.sharpConstant ∧
    ∃ D : ConvexDomain, D.area = 1 ∧
      torsionTheory.G D = ENNReal.ofReal d.sharpConstant :=
  conditional_exact_value torsionTheory d (ScalingLaw.proved torsionTheory) C

/-- Spectral formulation with the proved base theory and scaling.
The spectral reference bridge is the only proof parameter at this layer;
`second_exact_value` later applies this theorem to its constructed instance. -/
theorem exact_value_of_spectralBridge (a : ℝ) (φ : ℝ → ℝ)
    (B : SpectralBridge torsionTheory a φ) :
    torsionTheory.cStar = ENNReal.ofReal (Spectral.spectralConstant a φ) ∧
    ∃ D : ConvexDomain, D.carrier = Spectral.normalizedImage a φ ∧
      D.area = 1 ∧ torsionTheory.G D = ENNReal.ofReal (Spectral.spectralConstant a φ) := by
  simpa only [Spectral.spectralConstant, Spectral.normalizedImage, Complex.ofReal_inv] using
    conditional_spectral_exact_value torsionTheory (ScalingLaw.proved torsionTheory) a φ B

end Torsion
end

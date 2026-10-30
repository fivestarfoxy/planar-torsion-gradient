module

public import Torsion.MarkedBoundaryRegularity

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Constructed marked torsion flux and radial concavity

The flux is now an actual object obtained from weak torsion, odd reflection
and local Weyl regularity. No flux existence, comparison, homogeneity or
supermodularity assumptions occur in the theorems in this module.
-/

noncomputable section
open Set
open scoped Pointwise

namespace Torsion

/-- The actual marked torsion flux. It is set to zero on nonmarked sets;
only its values on marked domains are used. -/
def torsionFlux : Set Plane → ℝ := markedFlux markedFluxExistence_proved

/-- The chosen flux is realized by an actual weak torsion solution with a
continuous local marked representative and its finite inward limit. -/
theorem torsionFlux_spec {D : Set Plane} (hD : IsMarked D) :
    HasTorsionFlux D (torsionFlux D) := markedFlux_spec markedFluxExistence_proved hD

/-- The constructed flux agrees with every other genuine marked torsion
flux, independently of all a.e. representative and solution choices. -/
theorem HasTorsionFlux.eq_torsionFlux {D : Set Plane} {q : ℝ}
    (hq : HasTorsionFlux D q) (hD : IsMarked D) : q = torsionFlux D :=
  hq.unique (torsionFlux_spec hD) hD.1 hD.2.1

theorem torsionFlux_nonneg {D : Set Plane} (hD : IsMarked D) :
    0 ≤ torsionFlux D := (torsionFlux_spec hD).nonneg hD.2.1

/-- All three PDE laws used by the finite-dimensional and continuous radial
arguments are now proved for the actual constructed torsion flux. -/
theorem torsionFluxRules : RadialFluxConcavity.MarkedFluxRules torsionFlux :=
  markedFluxRules_of_exists markedFluxExistence_proved

theorem torsionFlux_mono {D E : Set Plane} (hD : IsMarked D) (hE : IsMarked E)
    (hDE : D ⊆ E) : torsionFlux D ≤ torsionFlux E :=
  torsionFluxRules.mono hD hE hDE

theorem torsionFlux_dilate {D : Set Plane} (hD : IsMarked D) (s : ℝ) (hs : 0 < s) :
    torsionFlux (s • D) = s * torsionFlux D := torsionFluxRules.homogeneous hD s hs

theorem torsionFlux_supermodular {D E : Set Plane} (hD : IsMarked D) (hE : IsMarked E) :
    torsionFlux D + torsionFlux E ≤ torsionFlux (D ∪ E) + torsionFlux (D ∩ E) :=
  torsionFluxRules.supermodular hD hE

/-- Theorem 3.6 for genuine weak torsion, with every marked-flux PDE and
regularity obligation discharged. -/
theorem torsionFlux_radial_concaveOn :
    ConcaveOn ℝ RadialFluxConcavity.positiveContinuousProfiles
      (fun R => torsionFlux (radialDomain R)) :=
  RadialFluxConcavity.radial_flux_concaveOn torsionFluxRules

end Torsion

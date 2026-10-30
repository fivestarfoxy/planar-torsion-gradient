module

public import Torsion.RestrictedSpectralSecondParity
public import Torsion.RestrictedSpectralOddSelection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Identification of the second and least odd eigenvalues below the even gap

The actual second eigenfunction has odd L² parity below the proved even
mean-zero gap. The genuine odd variational minimum gives the reverse
spectral comparison. The proved simplicity of the least odd eigenspace
then gives simplicity of the entire actual second eigenspace.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- The constructed least odd value is the actual second variational value
whenever the latter lies below the proved even-sector gap. -/
theorem leastOddEigenvalue_eq_secondEigenvalue_of_lt_even_gap
    (hupper : secondEigenvalue < (63 / 20 : ℝ)) :
    leastOddEigenvalue = secondEigenvalue := by
  have hae := secondEigenfunctionL2_eq_oddPart_ae_of_lt_even_gap hupper
  have heig := secondEigenfunctionL2_isRestrictedEigenfunction.congr_ae hae
  have hminimum := leastOddEigenvalue_variational _ heig.1
    (restrictedOddPart_odd secondEigenfunctionL2)
  have hself : energy (restrictedOddPart secondEigenfunctionL2) (restrictedOddPart secondEigenfunctionL2) =
      secondEigenvalue * (∫ x : ℝ, restrictedOddPart secondEigenfunctionL2 x ^ 2) := by
    simpa only [← pow_two] using heig.2.2 _ heig.1
  rw [hself] at hminimum
  have hmass : 0 < ∫ x : ℝ, restrictedOddPart secondEigenfunctionL2 x ^ 2 := by
    simpa only [← pow_two] using heig.square_integral_pos
  exact le_antisymm ((mul_le_mul_right hmass).mp hminimum) secondEigenvalue_le_leastOddEigenvalue

/-- Every genuine second eigenfunction belongs to the same one-dimensional
L² eigenspace as the selected odd, nonnegative-half eigenfunction, once the
actual second value is below the even gap. -/
theorem secondEigenfunction_simple_of_lt_even_gap
    (hupper : secondEigenvalue < (63 / 20 : ℝ)) {g : ℝ → ℝ}
    (hg : IsRestrictedEigenfunction secondEigenvalue g) :
    ∃ c : ℝ, g =ᵐ[volume] fun x => c * leastOddEigenfunctionL2 x := by
  have hparity := firstEigenfunctionL2_isRestrictedEigenfunction.eq_oddPart_ae_of_lt_even_gap
    firstEigenfunctionL2_even firstEigenvalue_variational hg
    firstEigenvalue_lt_secondEigenvalue hupper
  have hoddEig : IsRestrictedEigenfunction leastOddEigenvalue (restrictedOddPart g) := by
    rw [leastOddEigenvalue_eq_secondEigenvalue_of_lt_even_gap hupper]
    exact hg.congr_ae hparity
  obtain ⟨c, hc⟩ := leastOddEigenfunctionL2_simple hoddEig (restrictedOddPart_odd g)
  exact ⟨c, hparity.trans hc⟩

end Torsion.Spectral

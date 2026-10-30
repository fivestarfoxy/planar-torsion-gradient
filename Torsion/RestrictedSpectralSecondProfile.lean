import Torsion.RestrictedSpectralSecondEigenpair
import Torsion.RestrictedSpectralRegularRepresentative
import Torsion.RestrictedSpectralStrongMaximum

/-!
# A canonical interior analytic second eigenfunction

The derivative of the actual integrated height supplies a genuine regular
representative of the constructed second L² eigenpair. Its weak equation,
symmetry, normalization and simplicity are proved for the original restricted
Fourier problem. Endpoint Hölder regularity and concavity are not imposed by
this definition.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion.Spectral

/-- The actual interior analytic, odd, zero-exterior second eigenfunction,
with unit L² normalization and the nonnegative positive-half sign. -/
def secondEigenfunction : ℝ → ℝ := regularEigenfunction secondOddEigenfunctionL2

theorem secondEigenfunction_ae_eq :
    secondEigenfunction =ᵐ[volume] secondOddEigenfunctionL2 :=
  secondOddEigenfunctionL2_isRestrictedEigenfunction.regularEigenfunction_ae_eq
    secondOddEigenfunctionL2_odd

theorem secondEigenfunction_isRestrictedEigenfunction :
    IsRestrictedEigenfunction secondEigenvalue secondEigenfunction :=
  secondOddEigenfunctionL2_isRestrictedEigenfunction.regularEigenfunction_isRestrictedEigenfunction
    secondOddEigenfunctionL2_odd

theorem secondEigenfunction_odd : Function.Odd secondEigenfunction :=
  regularEigenfunction_odd _

theorem secondEigenfunction_zero_exterior (x : ℝ) (hx : 1 ≤ |x|) :
    secondEigenfunction x = 0 := regularEigenfunction_zero_exterior _ x hx

theorem secondEigenfunction_normalized : (∫ x : ℝ, secondEigenfunction x ^ 2) = 1 := by
  calc
    _ = ∫ x : ℝ, secondOddEigenfunctionL2 x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [secondEigenfunction_ae_eq] with x hx
      rw [hx]
    _ = 1 := secondOddEigenfunctionL2_normalized

theorem secondEigenfunction_analyticOnNhd :
    AnalyticOnNhd ℝ secondEigenfunction (Ioo (-1 : ℝ) 1) :=
  secondOddEigenfunctionL2_isRestrictedEigenfunction.regularEigenfunction_analyticOnNhd
    secondOddEigenfunctionL2_odd

theorem secondEigenfunction_contDiffOn :
    ContDiffOn ℝ ∞ secondEigenfunction (Ioo (-1 : ℝ) 1) :=
  secondOddEigenfunctionL2_isRestrictedEigenfunction.regularEigenfunction_contDiffOn
    secondOddEigenfunctionL2_odd

theorem secondEigenfunction_nonneg (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ secondEigenfunction x := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] secondOddEigenfunctionL2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact secondOddEigenfunctionL2_nonneg_half y hy.le
  exact secondOddEigenfunctionL2_isRestrictedEigenfunction.regularEigenfunction_nonneg
    secondOddEigenfunctionL2_odd hnonneg x hx

theorem secondEigenfunction_pos_ae :
    ∀ᵐ x : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < secondEigenfunction x := by
  filter_upwards [ae_restrict_of_ae secondEigenfunction_ae_eq,
    secondOddEigenfunctionL2_pos_ae] with x hx hp
  rw [hx]
  exact hp

/-- Strict positivity at every positive interior point follows from the
proved actual Cauchy-kernel strong maximum argument. -/
theorem secondEigenfunction_pos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < secondEigenfunction x := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] secondOddEigenfunctionL2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact secondOddEigenfunctionL2_nonneg_half y hy.le
  exact secondOddEigenfunctionL2_isRestrictedEigenfunction.regularEigenfunction_pos
    secondOddEigenfunctionL2_odd hnonneg x hx

theorem height_secondEigenfunction :
    height secondEigenfunction = height secondOddEigenfunctionL2 :=
  secondOddEigenfunctionL2_isRestrictedEigenfunction.height_regularEigenfunction
    secondOddEigenfunctionL2_odd

theorem secondEigenfunction_height_holder_half :
    ∃ C : ℝ≥0, HolderWith C (1 / 2) (height secondEigenfunction) :=
  secondEigenfunction_isRestrictedEigenfunction.1.height_holder_half

/-- Strict a.e. positivity already suffices for positivity of the original
integrated height; no endpoint continuity of the density is needed. -/
theorem height_pos_of_integrable_pos_ae {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hpos : ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < φ s)
    {x : ℝ} (hx : |x| < 1) : 0 < height φ x := by
  have hsubset : Ioo |x| (1 : ℝ) ⊆ Ioo (0 : ℝ) 1 :=
    fun s hs => ⟨lt_of_le_of_lt (abs_nonneg x) hs.1, hs.2⟩
  have hpos' : ∀ᵐ s : ℝ ∂volume.restrict (Ioo |x| 1), 0 < φ s :=
    ae_restrict_of_ae_restrict_of_subset hsubset hpos
  have hsupport : (volume.restrict (Ioo |x| 1)) (Function.support φ) =
      (volume.restrict (Ioo |x| 1)) univ := by
    apply measure_congr
    filter_upwards [hpos'] with s hs
    change (φ s ≠ 0) = True
    exact propext (iff_true_intro (ne_of_gt hs))
  rw [height, if_pos hx, integral_Icc_eq_integral_Ioo]
  apply (integral_pos_iff_support_of_nonneg_ae (hpos'.mono fun _ h => h.le) hφ.integrableOn).2
  rw [hsupport, Measure.restrict_apply_univ, Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hx)

theorem secondEigenfunction_height_pos {x : ℝ} (hx : |x| < 1) :
    0 < height secondEigenfunction x :=
  height_pos_of_integrable_pos_ae secondEigenfunction_isRestrictedEigenfunction.1.integrable
    secondEigenfunction_pos_ae hx

/-- Simplicity is expressed relative to the actual analytic representative,
for every original weak eigenfunction at the constructed second value. -/
theorem secondEigenfunction_simple {g : ℝ → ℝ}
    (hg : IsRestrictedEigenfunction secondEigenvalue g) :
    ∃ c : ℝ, g =ᵐ[volume] fun x => c * secondEigenfunction x := by
  obtain ⟨c, hc⟩ := secondOddEigenfunctionL2_simple hg
  refine ⟨c, ?_⟩
  filter_upwards [hc, secondEigenfunction_ae_eq] with x hx heq
  rw [heq]
  exact hx

/-- An unconditional existence theorem collecting the currently proved
second-profile properties. Strict positivity here is explicitly a.e.; no
endpoint regularity or concavity hypothesis is hidden in the statement. -/
theorem exists_second_analytic_simple_restricted_eigenfunction :
    ∃ φ : ℝ → ℝ, IsRestrictedEigenfunction secondEigenvalue φ ∧
      Function.Odd φ ∧ (∀ x : ℝ, 1 ≤ |x| → φ x = 0) ∧
      (∫ x : ℝ, φ x ^ 2) = 1 ∧ AnalyticOnNhd ℝ φ (Ioo (-1 : ℝ) 1) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ φ x) ∧
      (∀ᵐ x : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < φ x) ∧
      (∀ g : ℝ → ℝ, IsRestrictedEigenfunction secondEigenvalue g →
        ∃ c : ℝ, g =ᵐ[volume] fun x => c * φ x) :=
  ⟨secondEigenfunction, secondEigenfunction_isRestrictedEigenfunction,
    secondEigenfunction_odd, secondEigenfunction_zero_exterior,
    secondEigenfunction_normalized, secondEigenfunction_analyticOnNhd,
    secondEigenfunction_nonneg, secondEigenfunction_pos_ae,
    fun _ hg => secondEigenfunction_simple hg⟩

/-- The selected second variational eigenvalue has a normalized, simple,
odd, interior analytic eigenfunction strictly positive throughout `(0,1)`.
These are conclusions for the original weak Fourier problem. -/
theorem exists_second_positive_analytic_simple_restricted_eigenfunction :
    ∃ φ : ℝ → ℝ, IsRestrictedEigenfunction secondEigenvalue φ ∧
      Function.Odd φ ∧ (∀ x : ℝ, 1 ≤ |x| → φ x = 0) ∧
      (∫ x : ℝ, φ x ^ 2) = 1 ∧ AnalyticOnNhd ℝ φ (Ioo (-1 : ℝ) 1) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) ∧
      (∀ g : ℝ → ℝ, IsRestrictedEigenfunction secondEigenvalue g →
        ∃ c : ℝ, g =ᵐ[volume] fun x => c * φ x) :=
  ⟨secondEigenfunction, secondEigenfunction_isRestrictedEigenfunction,
    secondEigenfunction_odd, secondEigenfunction_zero_exterior,
    secondEigenfunction_normalized, secondEigenfunction_analyticOnNhd,
    secondEigenfunction_pos, fun _ hg => secondEigenfunction_simple hg⟩

end Torsion.Spectral

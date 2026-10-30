import Torsion.RestrictedSpectralOddGroundSign
import Torsion.RestrictedSpectralPositiveTest

/-!
# Non-null positive levels of the actual odd restricted eigenfunction

A countable positive-level cover selects a uniform positive threshold.
The original restricted support and odd reflection ensure that a nonzero
odd form member nonnegative on the positive half has a non-null positive
set inside (0,1). No continuity or strict positivity is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- A pointwise positive function on a non-null set is uniformly bounded
below by some positive threshold on a non-null part. This uses outer
measure only and requires neither measurability nor boundedness. -/
theorem exists_positive_level_inter_measure_ne_zero {f : ℝ → ℝ} {A : Set ℝ}
    (hA : volume A ≠ 0) (hpos : ∀ x ∈ A, 0 < f x) :
    ∃ η : ℝ, 0 < η ∧ volume (A ∩ {x : ℝ | η ≤ f x}) ≠ 0 := by
  let S : ℕ → Set ℝ := fun n => A ∩ {x : ℝ | 1 / ((n : ℝ) + 1) ≤ f x}
  have hcover : A ⊆ ⋃ n : ℕ, S n := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hpos x hx)
    exact mem_iUnion.2 ⟨n, hx, hn.le⟩
  have hUnion : volume (⋃ n : ℕ, S n) ≠ 0 := by
    intro hz
    exact hA (measure_mono_null hcover hz)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hUnion
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn.ne'⟩

/-- An actual nonzero odd restricted form member nonnegative on the
positive half has a non-null positive set inside the original interval. -/
theorem MemRestrictedFormDomain.positive_half_set_measure_ne_zero {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f)
    (hne : ¬ f =ᵐ[volume] 0)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f) :
    volume {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ 0 < f x} ≠ 0 := by
  intro hz
  have hnot : ∀ᵐ x : ℝ ∂volume, ¬(x ∈ Ioo (0 : ℝ) 1 ∧ 0 < f x) := by
    rw [ae_iff]
    simpa only [not_not] using hz
  apply hne
  apply ae_eq_zero_of_odd_ae_eq_zero_half hodd
  filter_upwards [ae_restrict_of_ae hnot, ae_restrict_of_ae hf.2.2.1,
    hnonneg, ae_restrict_mem measurableSet_Ioi] with x hxnot hxzero hxnonneg hx
  change f x = 0
  by_cases hx1 : x < 1
  · have hn : ¬ 0 < f x := fun hp => hxnot ⟨⟨hx, hx1⟩, hp⟩
    exact le_antisymm (le_of_not_gt hn) hxnonneg
  · exact hxzero (by intro hi; exact hx1 hi.2)

/-- The non-null positive-set theorem for the actual weak odd eigenfunction. -/
theorem IsRestrictedEigenfunction.positive_half_set_measure_ne_zero {a : ℝ} {f : ℝ → ℝ}
    (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f) :
    volume {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ 0 < f x} ≠ 0 :=
  hf.1.positive_half_set_measure_ne_zero hodd hf.2.1 hnonneg

/-- There is an actual non-null positive level subset of (0,1) for every
nonzero odd restricted form member of the stated half-line sign. -/
theorem MemRestrictedFormDomain.exists_positive_half_level {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f)
    (hne : ¬ f =ᵐ[volume] 0)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f) :
    ∃ η : ℝ, 0 < η ∧ volume {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ η ≤ f x} ≠ 0 := by
  obtain ⟨η, hη, hlevel⟩ := exists_positive_level_inter_measure_ne_zero
    (hf.positive_half_set_measure_ne_zero hodd hne hnonneg)
    (fun _ hx => hx.2)
  refine ⟨η, hη, ?_⟩
  intro hz
  apply hlevel
  apply measure_mono_null ?_ hz
  intro x hx
  exact ⟨hx.1.1, hx.2⟩

/-- The positive-level selection is constructed directly from the actual
weak eigenfunction and its proved half-line nonnegative sign. -/
theorem IsRestrictedEigenfunction.exists_positive_half_level {a : ℝ} {f : ℝ → ℝ}
    (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f) :
    ∃ η : ℝ, 0 < η ∧ volume {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ η ≤ f x} ≠ 0 :=
  hf.1.exists_positive_half_level hodd hf.2.1 hnonneg

end Torsion.Spectral

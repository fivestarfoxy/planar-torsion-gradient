import Torsion.RestrictedSpectralOddFoldCore
import Torsion.RestrictedSpectralOddFoldApproximation
import Torsion.RestrictedSpectralOddCore
import Torsion.RestrictedSpectralWeakClosure

/-!
# Actual folded absolute-value admission for the odd restricted form

Odd compact smooth approximants are folded with genuinely flat scalar
approximations. The proved four-quadrant real-space contraction bounds
their original Fourier energies. Their actual global L² limit is the
folded absolute value, so closed-graph weak compactness proves admission
and energy contraction in the original restricted form domain.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- The folded absolute value is nonnegative on the positive half line. -/
theorem oddFoldAbs_nonneg (f : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ oddFoldAbs f x := by
  rw [oddFoldAbs_of_nonneg hx]
  exact abs_nonneg _

/-- Odd folding preserves the actual squared L² pairing exactly. -/
theorem integral_oddFoldAbs_mul_self (f : ℝ → ℝ) :
    (∫ x : ℝ, oddFoldAbs f x * oddFoldAbs f x) = ∫ x : ℝ, f x * f x := by
  apply integral_congr_ae
  exact ae_of_all _ fun x => by simpa only [pow_two] using oddFoldAbs_sq f x

/-- A nonzero L² class remains nonzero after the actual odd absolute fold. -/
theorem oddFoldAbs_not_ae_zero {f : ℝ → ℝ} (hf : ¬ f =ᵐ[volume] 0) :
    ¬ oddFoldAbs f =ᵐ[volume] 0 := by
  intro hzero
  apply hf
  filter_upwards [hzero] with x hx
  simp only [Pi.zero_apply] at hx ⊢
  have h := oddFoldAbs_norm f x
  rw [hx, norm_zero] at h
  exact norm_eq_zero.mp h.symm

/-- The actual odd absolute fold belongs to the original restricted form
and contracts its original Fourier energy. No odd lattice closure or
quadrant comparison is assumed. -/
theorem MemRestrictedFormDomain.oddFoldAbs_energy_le {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f) :
    MemRestrictedFormDomain (oddFoldAbs f) ∧
      energy (oddFoldAbs f) (oddFoldAbs f) ≤ energy f f := by
  obtain ⟨v, hv, hL, _, hE⟩ := hf.exists_odd_core_approximation hodd
  let w : ℕ → ℝ → ℝ := fun n => oddFoldComp (oddFoldAbsApprox n) (v n)
  have hw : ∀ n, IsCore (w n) := fun n => (hv n).1.oddFoldAbsApprox (hv n).2 n
  have hbound : ∀ n, energy (w n) (w n) ≤ energy (v n) (v n) :=
    fun n => energy_oddFoldAbsApprox_le (hv n).1 (hv n).2 n
  have hfold : Tendsto (fun n => eLpNorm (fun x => w n x - oddFoldAbs f x) 2 volume)
      atTop (𝓝 0) :=
    tendsto_eLpNorm_oddFoldComp_joint hf.1 (fun n => (hv n).1.1.continuous.aestronglyMeasurable) hL
  exact memRestrictedFormDomain_of_core_energy_upper_tendsto (oddFoldAbs_memLp hf.1)
    hw hfold (Eventually.of_forall hbound) hE

/-- Concrete odd folded absolute-value closure of the original form. -/
theorem MemRestrictedFormDomain.oddFoldAbs {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f) :
    MemRestrictedFormDomain (oddFoldAbs f) := (hf.oddFoldAbs_energy_le hodd).1

theorem energy_oddFoldAbs_le {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f) :
    energy (oddFoldAbs f) (oddFoldAbs f) ≤ energy f f := (hf.oddFoldAbs_energy_le hodd).2

end Torsion.Spectral

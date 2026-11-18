module

public import Torsion.Proof.PaperGalerkinWeakEquation

@[expose] public section

/-! # The diagonal matrix of the restricted Dirichlet form on the sine modes -/

noncomputable section
open Set MeasureTheory Polynomial.Chebyshev
namespace Torsion.Galerkin

private theorem trialMode_energyIntegral (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (∫ x in Ioo (-1 : ℝ) 1, (k : ℝ) * (U ℝ ((k : ℤ) - 1)).eval x * trialMode l x) =
      if k = l then (k : ℝ) * Real.pi / 2 else 0 := by
  have hkl := chebyshevEnergyIntegral (k : ℤ) (l : ℤ) (by exact_mod_cast hk) (by exact_mod_cast hl)
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo] at hkl
  simp only [Int.cast_natCast, Nat.cast_inj] at hkl
  refine Eq.trans ?_ hkl
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  dsimp only
  rw [trialMode_sine l (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)]

/-- The Fourier-defined restricted Dirichlet form is exactly diagonal on
all positive-frequency Chebyshev sine modes. -/
theorem trialMode_energy (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    Spectral.energy (trialMode k) (trialMode l) =
      if k = l then (k : ℝ) * Real.pi / 2 else 0 := by
  rw [trialMode_weak_equation k hk (trialMode l) (trialMode_memRestrictedFormDomain l)]
  exact trialMode_energyIntegral k l hk hl

end Torsion.Galerkin

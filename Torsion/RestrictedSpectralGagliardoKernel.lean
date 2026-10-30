module

public import Torsion.RestrictedSpectralGagliardoDomain
public import Torsion.RestrictedSpectralLattice
public import Mathlib.MeasureTheory.Group.LIntegral

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two-point Gagliardo kernel of the actual restricted form

The translation seminorm is unchanged by a.e. representatives. For a
measurable representative, nonnegative Tonelli and translation invariance
identify it with the ordinary two-point difference kernel.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- A.e. changes in the density preserve the actual Gagliardo seminorm. -/
theorem gagliardoEnergy_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) :
    gagliardoEnergy f = gagliardoEnergy g := by
  unfold gagliardoEnergy
  apply lintegral_congr
  intro h
  apply lintegral_congr_ae
  have hshift : (fun x => f (x + h)) =ᵐ[volume] (fun x => g (x + h)) :=
    hfg.comp_tendsto (measurePreserving_add_right (volume : Measure ℝ) h).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hshift, hfg] with x hx hx'
  rw [hx, hx']

/-- The actual two-point nonnegative difference kernel is measurable. -/
theorem measurable_gagliardoKernel {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((f p.2 - f p.1) ^ 2 / (p.2 - p.1) ^ 2)) := by
  apply Measurable.ennreal_ofReal
  exact (((hf.comp measurable_snd).sub (hf.comp measurable_fst)).pow_const 2).div
    ((measurable_snd.sub measurable_fst).pow_const 2)

/-- The genuine real-space seminorm is exactly the two-point kernel,
ready for sign, irreducibility and odd-reflection arguments. -/
theorem gagliardoEnergy_eq_double {f : ℝ → ℝ} (hf : Measurable f) :
    gagliardoEnergy f =
      ∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal ((f y - f x) ^ 2 / (y - x) ^ 2) := by
  unfold gagliardoEnergy
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal
      ((f (p.2 + p.1) - f p.2) ^ 2 / p.1 ^ 2)) := by
    apply Measurable.ennreal_ofReal
    exact (((hf.comp (measurable_snd.add measurable_fst)).sub (hf.comp measurable_snd)).pow_const 2).div
      (measurable_fst.pow_const 2)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro x
  have h := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y : ℝ => ENNReal.ofReal ((f y - f x) ^ 2 / (y - x) ^ 2)) x
  simpa only [add_sub_cancel_right, add_sub_cancel_left, add_comm] using h

end Torsion.Spectral

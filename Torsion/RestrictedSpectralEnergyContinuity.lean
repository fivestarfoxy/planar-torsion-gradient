import Torsion.RestrictedSpectralSymmetry
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Continuity of the concrete restricted form along its defining approximants

The actual Fourier energy is the squared Hilbert norm of the existing
frequency-side half derivative, with its exact factor `1 / (2π)`.
Consequently convergence of the defining energy error gives convergence
of energies. The analogous L² assertion uses the actual `toLp` classes.
No spectral existence or compactness assumption is introduced.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform

namespace Torsion.Spectral

/-- Subtraction in the source's actual Fourier integral. -/
theorem fourier_sub {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    fourier (fun x => f x - g x) = fourier f - fourier g := by
  have heq : (fun x => f x - g x) = fun x => f x + (-1 : ℝ) * g x := by
    funext x
    ring
  rw [heq, fourier_add hf (hg.const_mul (-1)), fourier_const_mul]
  ext ξ
  simp [sub_eq_add_neg]

/-- Subtraction commutes with the concrete weighted Fourier transform. -/
theorem weightedFourier_sub {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    weightedFourier (fun x => f x - g x) = weightedFourier f - weightedFourier g := by
  ext ξ
  simp only [weightedFourier, fourier_sub hf hg, Pi.sub_apply, smul_sub]

/-- The exact energy normalization as a genuine Hilbert squared norm. -/
theorem energy_self_eq_norm_halfDerivative {f : ℝ → ℝ}
    (hf : Integrable f) (he : FiniteEnergy f) :
    energy f f = (1 / (2 * Real.pi)) * ‖halfDerivative f hf he‖ ^ 2 := by
  rw [energy_eq_inner_halfDerivative hf hf he he, real_inner_self_eq_norm_sq]

/-- The actual Fourier energy error is the Hilbert squared distance between
half derivatives. This identifies the original approximation norm. -/
theorem energy_sub_eq_norm_halfDerivative_sub {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hef : FiniteEnergy f) (heg : FiniteEnergy g) :
    energy (fun x => f x - g x) (fun x => f x - g x) =
      (1 / (2 * Real.pi)) *
        ‖halfDerivative f hf hef - halfDerivative g hg heg‖ ^ 2 := by
  rw [energy_self]
  calc
    _ = (1 / (2 * Real.pi)) *
        ∫ ξ : ℝ, inner (𝕜 := ℝ)
          ((halfDerivative f hf hef - halfDerivative g hg heg : Lp ℂ 2 volume) ξ)
          ((halfDerivative f hf hef - halfDerivative g hg heg : Lp ℂ 2 volume) ξ) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (halfDerivative f hf hef) (halfDerivative g hg heg),
        halfDerivative_ae f hf hef, halfDerivative_ae g hg heg] with ξ hsub hξf hξg
      dsimp only [Pi.sub_apply] at hsub
      have hW := congrFun (weightedFourier_sub hf hg) ξ
      simp only [Pi.sub_apply] at hW
      rw [hsub, hξf, hξg, ← hW,
        real_inner_self_eq_norm_sq, weightedFourier_norm_sq]
    _ = (1 / (2 * Real.pi)) *
        inner (𝕜 := ℝ) (halfDerivative f hf hef - halfDerivative g hg heg)
          (halfDerivative f hf hef - halfDerivative g hg heg) := by rw [L2.inner_def]
    _ = _ := by rw [real_inner_self_eq_norm_sq]

/-- Convergence of the actual energy errors forces convergence of the
actual diagonal energies, through the genuine Hilbert half derivatives. -/
theorem energy_tendsto_of_difference {f : ℝ → ℝ} {v : ℕ → ℝ → ℝ}
    (hf : Integrable f) (hv : ∀ n, Integrable (v n))
    (hef : FiniteEnergy f) (hev : ∀ n, FiniteEnergy (v n))
    (hlim : Tendsto (fun n => energy (fun x => v n x - f x)
      (fun x => v n x - f x)) atTop (𝓝 0)) :
    Tendsto (fun n => energy (v n) (v n)) atTop (𝓝 (energy f f)) := by
  let V : ℕ → Lp ℂ 2 (volume : Measure ℝ) := fun n => halfDerivative (v n) (hv n) (hev n)
  let F : Lp ℂ 2 (volume : Measure ℝ) := halfDerivative f hf hef
  have heq (n : ℕ) : ‖V n - F‖ ^ 2 = (2 * Real.pi) *
      energy (fun x => v n x - f x) (fun x => v n x - f x) := by
    rw [energy_sub_eq_norm_halfDerivative_sub (hv n) hf (hev n) hef]
    dsimp only [V, F]
    field_simp
  have hsq : Tendsto (fun n => ‖V n - F‖ ^ 2) atTop (𝓝 0) := by
    simpa only [heq, mul_zero] using hlim.const_mul (2 * Real.pi)
  have hnorm : Tendsto (fun n => ‖V n - F‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq
  have hV : Tendsto V atTop (𝓝 F) := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have hnormsq := (hV.norm.pow 2).const_mul (1 / (2 * Real.pi))
  have hE (n : ℕ) : energy (v n) (v n) = (1 / (2 * Real.pi)) * ‖V n‖ ^ 2 :=
    energy_self_eq_norm_halfDerivative (hv n) (hev n)
  have hF : energy f f = (1 / (2 * Real.pi)) * ‖F‖ ^ 2 :=
    energy_self_eq_norm_halfDerivative hf hef
  simpa only [hE, hF] using hnormsq

/-- The actual square integral is the norm squared of its real L² class. -/
theorem integral_sq_eq_norm_toLp_sq {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    (∫ x : ℝ, (f x) ^ 2) = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- L² convergence of the concrete defining approximants forces convergence
of their actual square integrals. -/
theorem integral_sq_tendsto_of_eLpNorm_sub {f : ℝ → ℝ} {v : ℕ → ℝ → ℝ}
    (hf : MemLp f 2 volume) (hv : ∀ n, MemLp (v n) 2 volume)
    (hlim : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : ℝ, (v n x) ^ 2) atTop (𝓝 (∫ x : ℝ, (f x) ^ 2)) := by
  have hV : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hf.toLp f)) := by
    apply tendsto_iff_edist_tendsto_0.mpr
    simpa only [Lp.edist_toLp_toLp] using hlim
  have hnormsq := hV.norm.pow 2
  have hE (n : ℕ) : (∫ x : ℝ, (v n x) ^ 2) = ‖(hv n).toLp (v n)‖ ^ 2 :=
    integral_sq_eq_norm_toLp_sq (hv n)
  have hF : (∫ x : ℝ, (f x) ^ 2) = ‖hf.toLp f‖ ^ 2 := integral_sq_eq_norm_toLp_sq hf
  simpa only [hE, hF] using hnormsq

end Torsion.Spectral

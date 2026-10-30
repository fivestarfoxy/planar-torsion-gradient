import Torsion.RestrictedSpectralForm

/-!
# Algebra of the concrete restricted Fourier energy

The half derivative is the actual weighted Fourier transform, embedded in
the usual complex L² space. This provides the form's bilinear estimates.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform

namespace Torsion.Spectral

theorem fourier_add {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    fourier (fun x => f x + g x) = fourier f + fourier g := by
  ext ξ
  change fourier (fun x => f x + g x) ξ = fourier f ξ + fourier g ξ
  simp only [fourier_eq_mathlib, Complex.ofReal_add]
  have h := VectorFourier.fourierIntegral_add
    (L := innerₗ ℝ) (μ := volume) Real.continuous_fourierChar continuous_inner
    (Complex.ofRealCLM.integrable_comp hf) (Complex.ofRealCLM.integrable_comp hg)
  exact congrFun h (ξ / (2 * Real.pi))

theorem fourier_const_mul (c : ℝ) (f : ℝ → ℝ) :
    fourier (fun x => c * f x) = fun ξ => (c : ℂ) * fourier f ξ := by
  ext ξ
  unfold fourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    push_cast
    ring

/-- The frequency-side half derivative in the source's Fourier convention. -/
def weightedFourier (f : ℝ → ℝ) (ξ : ℝ) : ℂ := Real.sqrt |ξ| • fourier f ξ

theorem weightedFourier_norm_sq (f : ℝ → ℝ) (ξ : ℝ) :
    ‖weightedFourier f ξ‖ ^ 2 = |ξ| * ‖fourier f ξ‖ ^ 2 := by
  simp only [weightedFourier, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (abs_nonneg _)]

theorem weightedFourier_continuous {f : ℝ → ℝ} (hf : Integrable f) :
    Continuous (weightedFourier f) :=
  (Real.continuous_sqrt.comp continuous_abs).smul (fourier_continuous hf)

theorem finiteEnergy_iff_memLp_weightedFourier {f : ℝ → ℝ} (hf : Integrable f) :
    FiniteEnergy f ↔ MemLp (weightedFourier f) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (weightedFourier_continuous hf).aestronglyMeasurable]
  simp only [weightedFourier_norm_sq]
  rfl

theorem weightedFourier_add {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    weightedFourier (fun x => f x + g x) = weightedFourier f + weightedFourier g := by
  ext ξ
  simp only [weightedFourier, fourier_add hf hg, Pi.add_apply, smul_add]

theorem weightedFourier_const_mul (c : ℝ) (f : ℝ → ℝ) :
    weightedFourier (fun x => c * f x) = c • weightedFourier f := by
  ext ξ
  simp only [weightedFourier, fourier_const_mul, Pi.smul_apply, Complex.real_smul]
  ring

theorem FiniteEnergy.add {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hef : FiniteEnergy f) (heg : FiniteEnergy g) : FiniteEnergy (fun x => f x + g x) := by
  apply (finiteEnergy_iff_memLp_weightedFourier (hf.add hg)).mpr
  change MemLp (weightedFourier (fun x => f x + g x)) 2 volume
  rw [weightedFourier_add hf hg]
  exact ((finiteEnergy_iff_memLp_weightedFourier hf).mp hef).add
    ((finiteEnergy_iff_memLp_weightedFourier hg).mp heg)

theorem FiniteEnergy.const_mul {f : ℝ → ℝ} (hf : Integrable f)
    (hef : FiniteEnergy f) (c : ℝ) : FiniteEnergy (fun x => c * f x) := by
  rw [finiteEnergy_iff_memLp_weightedFourier (hf.const_mul c), weightedFourier_const_mul]
  exact ((finiteEnergy_iff_memLp_weightedFourier hf).mp hef).const_smul c

/-- An actual L² half derivative, with its source Fourier normalization. -/
def halfDerivative (f : ℝ → ℝ) (hf : Integrable f) (he : FiniteEnergy f) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ((finiteEnergy_iff_memLp_weightedFourier hf).mp he).toLp (weightedFourier f)

theorem halfDerivative_ae (f : ℝ → ℝ) (hf : Integrable f) (he : FiniteEnergy f) :
    (halfDerivative f hf he : ℝ → ℂ) =ᵐ[volume] weightedFourier f :=
  ((finiteEnergy_iff_memLp_weightedFourier hf).mp he).coeFn_toLp

theorem weightedFourier_inner (f g : ℝ → ℝ) (ξ : ℝ) :
    inner (𝕜 := ℝ) (weightedFourier f ξ) (weightedFourier g ξ) =
      |ξ| * (fourier f ξ * star (fourier g ξ)).re := by
  rw [weightedFourier, weightedFourier, real_inner_smul_left, real_inner_smul_right]
  have hs : Real.sqrt |ξ| * Real.sqrt |ξ| = |ξ| := Real.mul_self_sqrt (abs_nonneg ξ)
  rw [← mul_assoc, hs]
  simp only [Complex.inner, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The integral bilinear energy is the genuine real Hilbert pairing of the
frequency-side half derivatives, with the exact factor `1/(2π)`. -/
theorem energy_eq_inner_halfDerivative {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hef : FiniteEnergy f) (heg : FiniteEnergy g) :
    energy f g = (1 / (2 * Real.pi)) *
      inner (𝕜 := ℝ) (halfDerivative f hf hef) (halfDerivative g hg heg) := by
  rw [L2.inner_def]
  unfold energy
  congr 1
  apply integral_congr_ae
  filter_upwards [halfDerivative_ae f hf hef, halfDerivative_ae g hg heg] with ξ hξf hξg
  rw [hξf, hξg, weightedFourier_inner]

theorem energy_integrand_integrable {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hef : FiniteEnergy f) (heg : FiniteEnergy g) :
    Integrable (fun ξ : ℝ => |ξ| * (fourier f ξ * star (fourier g ξ)).re) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (halfDerivative f hf hef)
    (halfDerivative g hg heg)).congr
  filter_upwards [halfDerivative_ae f hf hef, halfDerivative_ae g hg heg] with ξ hξf hξg
  rw [hξf, hξg, weightedFourier_inner]

/-- Real bilinearity of the actual Fourier form in a finite-energy right
argument. The integrability is proved by its actual weighted L² realization. -/
theorem energy_add_right {f g h : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hef : FiniteEnergy f) (heg : FiniteEnergy g) (heh : FiniteEnergy h) :
    energy f (fun x => g x + h x) = energy f g + energy f h := by
  unfold energy
  rw [← mul_add, ← integral_add
    (energy_integrand_integrable hf hg hef heg)
    (energy_integrand_integrable hf hh hef heh)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    rw [fourier_add hg hh]
    simp only [Pi.add_apply, star_add, mul_add, Complex.add_re]

/-- Scalar bilinearity with the exact real source normalization. -/
theorem energy_const_mul_right (f g : ℝ → ℝ) (c : ℝ) :
    energy f (fun x => c * g x) = c * energy f g := by
  unfold energy
  calc
    _ = (1 / (2 * Real.pi)) * ∫ ξ : ℝ,
        c * (|ξ| * (fourier f ξ * star (fourier g ξ)).re) := by
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun ξ => by
        rw [fourier_const_mul]
        simp only [star_mul, Complex.star_def, Complex.conj_ofReal,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, zero_mul, add_zero, zero_add, sub_zero]
        ring
    _ = _ := by rw [integral_const_mul]; ring

/-- Real bilinearity in the finite-energy left argument. -/
theorem energy_add_left {f g h : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hef : FiniteEnergy f) (heg : FiniteEnergy g) (heh : FiniteEnergy h) :
    energy (fun x => f x + g x) h = energy f h + energy g h := by
  rw [energy_symm, energy_add_right hh hf hg heh hef heg,
    energy_symm h f, energy_symm h g]

/-- Scalar bilinearity in the left argument. -/
theorem energy_const_mul_left (c : ℝ) (f g : ℝ → ℝ) :
    energy (fun x => c * f x) g = c * energy f g := by
  rw [energy_symm, energy_const_mul_right, energy_symm g f]

end Torsion.Spectral

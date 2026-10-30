module

public import Torsion.FourierHilbertHeight
public import Torsion.CauchyTransformRealBoundary
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Absolute Fourier pairing for the conjugate Poisson kernel

At positive height the sign multiplier is integrable. Two ordinary Fubini
interchanges identify its bilinear Fourier pairing with the actual real
Cauchy kernel. No principal-value or Hilbert-multiplier theorem is assumed.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- Fubini for an integrable frequency weight and an integrable spatial
function, with a real Fourier phase of arbitrary sign. -/
theorem integral_fourier_phase_pairing {h k : ℝ → ℂ}
    (hh : Integrable h) (hk : Integrable k) (r : ℝ) :
    (∫ ξ : ℝ, h ξ * ∫ x : ℝ,
      Complex.exp (((r * x * ξ : ℝ) : ℂ) * Complex.I) * k x) =
      ∫ x : ℝ, k x * ∫ ξ : ℝ, h ξ *
        Complex.exp (((r * x * ξ : ℝ) : ℂ) * Complex.I) := by
  have hp : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (((r * p.2 * p.1 : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have hi : Integrable (fun p : ℝ × ℝ => h p.1 *
      (Complex.exp (((r * p.2 * p.1 : ℝ) : ℂ) * Complex.I) * k p.2)) := by
    apply (hh.norm.mul_prod hk.norm).mono'
    · exact hh.1.comp_fst.mul (hp.aestronglyMeasurable.mul hk.1.comp_snd)
    · exact ae_of_all _ fun p => by simp [norm_mul, Complex.norm_exp]
  calc
    _ = ∫ ξ : ℝ, ∫ x : ℝ, h ξ *
        (Complex.exp (((r * x * ξ : ℝ) : ℂ) * Complex.I) * k x) := by
      simp only [integral_const_mul]
    _ = ∫ x : ℝ, ∫ ξ : ℝ, h ξ *
        (Complex.exp (((r * x * ξ : ℝ) : ℂ) * Complex.I) * k x) :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun ξ => by ring

/-- The source-normalized Fourier transform has its genuine L¹ bound. -/
theorem norm_fourier_le_integral_norm (f : ℝ → ℝ) (ξ : ℝ) :
    ‖fourier f ξ‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  unfold fourier
  apply (norm_integral_le_integral_norm _).trans_eq
  congr 1
  funext x
  simp [norm_mul, Complex.norm_exp]

/-- Complex conjugation of the real Fourier transform reverses the phase. -/
theorem star_fourier_eq_integral_phase (g : ℝ → ℝ) (ξ : ℝ) :
    star (fourier g ξ) = ∫ x : ℝ,
      Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) * (g x : ℂ) := by
  unfold fourier
  rw [Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_ofReal,
      Complex.conj_I, neg_mul, mul_neg, neg_neg]

/-- The damped Fourier transform is actually integrable, from the L¹
Fourier bound and exponential damping. -/
theorem integrable_dampedSignMultiplier_fourier {f : ℝ → ℝ} {y : ℝ}
    (hf : Integrable f) (hy : 0 < y) :
    Integrable (fun ξ : ℝ => dampedSignMultiplier y ξ * fourier f ξ) := by
  apply (((integrable_dampedSignMultiplier hy).norm).mul_const (∫ x : ℝ, ‖f x‖)).mono'
  · exact (integrable_dampedSignMultiplier hy).1.mul (fourier_continuous hf).aestronglyMeasurable
  · exact ae_of_all _ fun ξ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_fourier_le_integral_norm f ξ) (norm_nonneg _)

/-- Absolute integrability of the full damped Fourier pairing. -/
theorem integrable_dampedSignMultiplier_fourier_pairing {f g : ℝ → ℝ} {y : ℝ}
    (hf : Integrable f) (hg : Integrable g) (hy : 0 < y) :
    Integrable (fun ξ : ℝ => dampedSignMultiplier y ξ * fourier f ξ * star (fourier g ξ)) := by
  apply (((integrable_dampedSignMultiplier_fourier hf hy).norm).mul_const
    (∫ x : ℝ, ‖g x‖)).mono'
  · exact (integrable_dampedSignMultiplier_fourier hf hy).1.mul
      (fourier_continuous hg).star.aestronglyMeasurable
  · exact ae_of_all _ fun ξ => by
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (norm_fourier_le_integral_norm g ξ) (norm_nonneg _)

/-- The unnormalized multiplier pairing is the physical Cauchy kernel
pairing with its exact factor `-2`. -/
theorem integral_dampedSignMultiplier_fourier_pairing {f g : ℝ → ℝ} {y : ℝ}
    (hf : Integrable f) (hg : Integrable g) (hy : 0 < y) :
    (∫ ξ : ℝ, dampedSignMultiplier y ξ * fourier f ξ * star (fourier g ξ)) =
      ∫ x : ℝ, (g x : ℂ) * ∫ s : ℝ, (f s : ℂ) *
        ((-2 * (x - s) / ((x - s) ^ 2 + y ^ 2) : ℝ) : ℂ) := by
  have hfc : Integrable (fun s => (f s : ℂ)) := Complex.ofRealCLM.integrable_comp hf
  have hgc : Integrable (fun x => (g x : ℂ)) := Complex.ofRealCLM.integrable_comp hg
  calc
    _ = ∫ x : ℝ, (g x : ℂ) * ∫ ξ : ℝ,
        (dampedSignMultiplier y ξ * fourier f ξ) *
          Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) := by
      simp_rw [star_fourier_eq_integral_phase]
      simpa only [one_mul] using integral_fourier_phase_pairing
        (integrable_dampedSignMultiplier_fourier hf hy) hgc 1
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        congr 1
        calc
          _ = ∫ ξ : ℝ, (dampedSignMultiplier y ξ *
              Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I)) *
                ∫ s : ℝ, Complex.exp (((-1 * s * ξ : ℝ) : ℂ) * Complex.I) * (f s : ℂ) := by
            apply integral_congr_ae
            exact ae_of_all _ fun ξ => by
              dsimp only
              have heq : (∫ s : ℝ, Complex.exp (((-1 * s * ξ : ℝ) : ℂ) * Complex.I) * (f s : ℂ)) =
                  fourier f ξ := by
                unfold fourier
                apply integral_congr_ae
                exact ae_of_all _ fun s => by
                  dsimp only
                  have he : (((-1 * s * ξ : ℝ) : ℂ) * Complex.I) =
                      -((s * ξ : ℝ) : ℂ) * Complex.I := by push_cast; ring
                  rw [he]
              rw [heq]
              ring
          _ = ∫ s : ℝ, (f s : ℂ) * ∫ ξ : ℝ,
              (dampedSignMultiplier y ξ * Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I)) *
                Complex.exp (((-1 * s * ξ : ℝ) : ℂ) * Complex.I) :=
            integral_fourier_phase_pairing (integrable_dampedSignMultiplier_phase hy x) hfc (-1)
          _ = _ := by
            apply integral_congr_ae
            exact ae_of_all _ fun s => by
              dsimp only
              congr 1
              calc
                _ = ∫ ξ : ℝ, dampedSignMultiplier y ξ *
                    Complex.exp ((((x - s) * ξ : ℝ) : ℂ) * Complex.I) := by
                  apply integral_congr_ae
                  exact ae_of_all _ fun ξ => by
                    dsimp only
                    have he : (((x * ξ : ℝ) : ℂ) * Complex.I) +
                        (((-1 * s * ξ : ℝ) : ℂ) * Complex.I) =
                        ((((x - s) * ξ : ℝ) : ℂ) * Complex.I) := by push_cast; ring
                    rw [mul_assoc, ← Complex.exp_add, he]
                _ = _ := integral_dampedSignMultiplier_phase hy (x - s)

/-- Positive-height Fourier/Hilbert pairing with the exact source
normalization `1/(2π)` and the actual real Cauchy kernel. -/
theorem damped_hilbert_fourier_pairing {f g : ℝ → ℝ} {y : ℝ}
    (hf : Integrable f) (hg : Integrable g) (hy : 0 < y) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ ξ : ℝ, dampedSignMultiplier y ξ * fourier f ξ * star (fourier g ξ)) =
      ∫ x : ℝ, (g x : ℂ) * ∫ s : ℝ, (f s : ℂ) *
        ((-(x - s) / (Real.pi * ((x - s) ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
  rw [integral_dampedSignMultiplier_fourier_pairing hf hg hy, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [mul_left_comm, ← integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun s => by
      dsimp only
      have hd : (x - s) ^ 2 + y ^ 2 ≠ 0 := by positivity
      have hk : (1 / (2 * Real.pi)) *
          (-2 * (x - s) / ((x - s) ^ 2 + y ^ 2)) =
          -(x - s) / (Real.pi * ((x - s) ^ 2 + y ^ 2)) := by
        field_simp [Real.pi_ne_zero, hd]
      rw [mul_left_comm, ← Complex.ofReal_mul, hk]

/-- The actual full-line conjugate-Poisson kernel is the real part of the
original interval Cauchy transform for zero-exterior continuous data. -/
theorem integral_realCauchy_kernel_eq {f : ℝ → ℝ}
    (hf : Continuous f) (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    (∫ s : ℝ, f s * (-(x - s) /
      (Real.pi * ((x - s) ^ 2 + y ^ 2)))) =
      (realCauchy f ((x : ℂ) + (y : ℂ) * Complex.I)).re := by
  have hz : (x : ℂ) + (y : ℂ) * Complex.I ∈ upperHalfPlane := by
    simpa [upperHalfPlane] using hy
  rw [realCauchy_re_eq_kernel hf hz]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  calc
    _ = ∫ s in Icc (-1 : ℝ) 1, f s * (-(x - s) /
        (Real.pi * ((x - s) ^ 2 + y ^ 2))) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro s hs
      have hn : 1 ≤ |s| := le_of_not_gt (fun h => hs (abs_le.1 h.le))
      rw [hzero s hn, zero_mul]
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro s _
      dsimp only
      have hs : (s - x) ^ 2 = (x - s) ^ 2 := by ring
      rw [hs]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The actual positive-height half-Laplacian pairing of the integrated
height is exactly the physical real Cauchy pairing of the odd density. -/
theorem damped_energy_height_eq_realCauchy_pairing {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) (hψ : Integrable ψ)
    {y : ℝ} (hy : 0 < y) :
    (1 / (2 * Real.pi)) * ∫ ξ : ℝ,
      Real.exp (-y * |ξ|) * (|ξ| *
        (fourier (height φ) ξ * star (fourier ψ ξ)).re) =
      ∫ x : ℝ, ψ x * (realCauchy φ ((x : ℂ) + (y : ℂ) * Complex.I)).re := by
  have hφi : Integrable φ :=
    hφ.integrable_of_hasCompactSupport (cauchyDensity_hasCompactSupport hzero)
  have h := damped_hilbert_fourier_pairing hφi hψ hy
  have hr : (∫ x : ℝ, (ψ x : ℂ) * ∫ s : ℝ, (φ s : ℂ) *
      ((-(x - s) / (Real.pi * ((x - s) ^ 2 + y ^ 2)) : ℝ) : ℂ)) =
      ((∫ x : ℝ, ψ x * ∫ s : ℝ, φ s *
        (-(x - s) / (Real.pi * ((x - s) ^ 2 + y ^ 2)))) : ℝ) := by
    simp only [← Complex.ofReal_mul, integral_complex_ofReal]
  rw [hr] at h
  have hre := congrArg Complex.re h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hre
  have hire : (∫ ξ : ℝ, dampedSignMultiplier y ξ * fourier φ ξ * star (fourier ψ ξ)).re =
      ∫ ξ : ℝ, (dampedSignMultiplier y ξ * fourier φ ξ * star (fourier ψ ξ)).re :=
    (integral_re (integrable_dampedSignMultiplier_fourier_pairing hφi hψ hy)).symm
  rw [hire] at hre
  simp_rw [dampedSignMultiplier_pairing_re_height hφ hodd hzero] at hre
  rw [hre]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [integral_realCauchy_kernel_eq hφ hzero hy x]

end Torsion.Spectral

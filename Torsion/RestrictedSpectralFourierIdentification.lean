import Torsion.RestrictedSpectralSchwartzFourier

/-! Actual global Fourier identification by Schwartz test separation. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- A genuine global weak equation tested by real Schwartz functions
identifies the actual L¹ Fourier transform of its right-hand-side density
with the original half-Laplacian multiplier. -/
theorem fourier_eq_abs_mul_of_schwartz_equation {f q : ℝ → ℝ}
    (hf : Integrable f) (hq : Integrable q)
    (hweak : ∀ S : 𝓢(ℝ, ℝ), energy f S = ∫ x : ℝ, q x * S x) :
    ∀ ξ : ℝ, fourier q ξ = ((|ξ| : ℝ) : ℂ) * fourier f ξ := by
  let P : ℝ := 2 * Real.pi
  have hP : 0 < P := by dsimp [P]; positivity
  let D : ℝ → ℂ := fun t => fourier q (P * t) - ((|P * t| : ℝ) : ℂ) * fourier f (P * t)
  have hDc : Continuous D := by
    dsimp only [D]
    exact ((fourier_continuous hq).comp (continuous_const.mul continuous_id)).sub
      ((Complex.continuous_ofReal.comp ((continuous_const.mul continuous_id).abs)).mul
        ((fourier_continuous hf).comp (continuous_const.mul continuous_id)))
  have hzero : D =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hDc.locallyIntegrable
    intro η hη hcη
    let T := compactSmoothSchwartz hη hcη
    let S := (SchwartzMap.fourierTransformCLE ℂ).symm T
    have hFS (ξ : ℝ) : complexSourceFourier S ξ = (η (ξ / P) : ℂ) := by
      exact congrArg (fun W : 𝓢(ℝ, ℂ) => W (ξ / P))
        ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply T)
    have hw := complex_schwartz_equation_of_real hf hq hweak S
    have hqpair := integral_fourier_complexSchwartz_pairing hq S
    have hif := integrable_weighted_complexSchwartz_pairing hf S 1
    have hiq := integrable_weighted_complexSchwartz_pairing hq S 0
    simp only [pow_one, Real.norm_eq_abs] at hif
    simp only [pow_zero, Complex.ofReal_one, one_mul] at hiq
    have hsource : (∫ ξ : ℝ, (fourier q ξ - ((|ξ| : ℝ) : ℂ) * fourier f ξ) *
        (η (ξ / P) : ℂ)) = 0 := by
      have heq : (fun ξ : ℝ => (fourier q ξ - ((|ξ| : ℝ) : ℂ) * fourier f ξ) *
          (η (ξ / P) : ℂ)) = fun ξ =>
        fourier q ξ * star (complexSourceFourier S ξ) -
          ((|ξ| : ℝ) : ℂ) * (fourier f ξ * star (complexSourceFourier S ξ)) := by
        funext ξ
        rw [hFS]
        simp only [Complex.star_def, Complex.conj_ofReal]
        ring
      rw [heq, integral_sub hiq hif, hqpair, hw, sub_self]
    have hscale := Measure.integral_comp_div (fun t : ℝ => D t * (η t : ℂ)) P
    have hleft : (∫ t : ℝ, D (t / P) * (η (t / P) : ℂ)) = 0 := by
      convert hsource using 1
      congr 1
      funext t
      dsimp only [D]
      rw [mul_div_cancel₀ _ hP.ne']
    rw [hleft] at hscale
    have hId : (∫ t : ℝ, D t * (η t : ℂ)) = 0 := by
      have hscale' : (0 : ℂ) = (P : ℂ) * ∫ t : ℝ, D t * (η t : ℂ) := by
        simpa only [smul_eq_mul, abs_of_pos hP] using hscale
      exact (mul_eq_zero.mp hscale'.symm).resolve_left (Complex.ofReal_ne_zero.mpr hP.ne')
    convert hId using 1
    congr 1
    funext t
    simp only [Complex.real_smul, mul_comm]
  have hD : D = 0 := Measure.eq_of_ae_eq hzero hDc continuous_const
  intro ξ
  have h := congrFun hD (ξ / P)
  change fourier q (P * (ξ / P)) - ((|P * (ξ / P)| : ℝ) : ℂ) *
    fourier f (P * (ξ / P)) = 0 at h
  rw [mul_div_cancel₀ _ hP.ne'] at h
  exact sub_eq_zero.mp h

end Torsion.Spectral

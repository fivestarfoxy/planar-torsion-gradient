module

public import Torsion.PhysicalCauchyTorsion
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Strict positivity of the physical Cauchy candidate

The actual candidate is one half of a Poisson variance.  The variance is
strictly positive because the Poisson mean of the height is positive while
the height vanishes on an exterior interval.  This uses the explicit
integrals rather than a maximum principle or an assumed weak-torsion
identification.
-/

noncomputable section
open Set MeasureTheory

namespace Torsion.Spectral

/-- The fixed-kernel Poisson integrand is genuinely integrable for every
continuous density with the prescribed compact support. -/
theorem poissonExtension_integrand_integrable {f : ℝ → ℝ}
    (hf : Continuous f) (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) (z : Plane) :
    Integrable (fun t : ℝ => poissonDensity t * f (z.re + z.im * t)) := by
  obtain ⟨B, hB⟩ := (cauchyDensity_hasCompactSupport hzero).exists_bound_of_continuous hf
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      poissonDensity t * f (z.re + z.im * t)) :=
    (poissonDensity_continuous.mul
      (hf.comp (continuous_const.add (continuous_const.mul continuous_id)))).aestronglyMeasurable
  apply (poissonDensity_integrable.mul_const B).mono' hmeas
  exact ae_of_all _ fun t => by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (poissonDensity_nonneg t)]
    exact mul_le_mul_of_nonneg_left (hB _) (poissonDensity_nonneg t)

/-- The exact variance identity for the probability measure with density
`poissonDensity`, with every term justified as an actual Bochner integral. -/
theorem poissonExtension_variance {f : ℝ → ℝ}
    (hf : Continuous f) (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) (z : Plane) :
    poissonExtension (fun s => (f s) ^ 2) z - (poissonExtension f z) ^ 2 =
      ∫ t : ℝ, poissonDensity t *
        (f (z.re + z.im * t) - poissonExtension f z) ^ 2 := by
  let m := poissonExtension f z
  have hi := poissonExtension_integrand_integrable hf hzero z
  have hi2 := poissonExtension_integrand_integrable (hf.pow 2)
    (fun s hs => by rw [hzero s hs]; norm_num) z
  have hc := poissonDensity_integrable.const_mul (m ^ 2)
  have hpoint (t : ℝ) : poissonDensity t * (f (z.re + z.im * t) - m) ^ 2 =
      (poissonDensity t * (f (z.re + z.im * t)) ^ 2 -
        (2 * m) * (poissonDensity t * f (z.re + z.im * t))) +
          m ^ 2 * poissonDensity t := by ring
  calc
    _ = (∫ t : ℝ, poissonDensity t * (f (z.re + z.im * t)) ^ 2) -
        (2 * m) * (∫ t : ℝ, poissonDensity t * f (z.re + z.im * t)) +
          m ^ 2 * (∫ t : ℝ, poissonDensity t) := by
      rw [integral_poissonDensity]
      change poissonExtension (fun s => (f s) ^ 2) z - m ^ 2 = _
      change _ = poissonExtension (fun s => (f s) ^ 2) z - (2 * m) * m + m ^ 2 * 1
      ring
    _ = ∫ t : ℝ, (poissonDensity t * (f (z.re + z.im * t)) ^ 2 -
        (2 * m) * (poissonDensity t * f (z.re + z.im * t))) +
          m ^ 2 * poissonDensity t := by
      have hsum := integral_add (hi2.sub (hi.const_mul (2 * m))) hc
      have hsub := integral_sub hi2 (hi.const_mul (2 * m))
      simp only [Pi.sub_apply, integral_const_mul] at hsum hsub
      rw [hsub] at hsum
      exact hsum.symm
    _ = _ := integral_congr_ae (ae_of_all _ fun t => (hpoint t).symm)

/-- The variance integrand itself is integrable, as follows from the
integrable square, linear and constant terms in its exact expansion. -/
theorem poissonExtension_variance_integrable {f : ℝ → ℝ}
    (hf : Continuous f) (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) (z : Plane) :
    Integrable (fun t : ℝ => poissonDensity t *
      (f (z.re + z.im * t) - poissonExtension f z) ^ 2) := by
  let m := poissonExtension f z
  have hi := poissonExtension_integrand_integrable hf hzero z
  have hi2 := poissonExtension_integrand_integrable (hf.pow 2)
    (fun s hs => by rw [hzero s hs]; norm_num) z
  apply ((hi2.sub (hi.const_mul (2 * m))).add
    (poissonDensity_integrable.const_mul (m ^ 2))).congr
  exact ae_of_all _ fun t => by dsimp [m]; ring

theorem poissonDensity_pos (t : ℝ) : 0 < poissonDensity t := by
  unfold poissonDensity
  positivity

/-- The imaginary auxiliary transform is exactly one half of the Poisson
extension of the squared height. -/
theorem auxiliary_im_eq_half_poissonExtension {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : Plane} (hz : z ∈ upperHalfPlane) :
    (auxiliary φ z).im = poissonExtension (fun s => (height φ s) ^ 2) z / 2 := by
  have heq : auxiliary φ z = (1 / 2 : ℂ) * realCauchy (fun s => (height φ s) ^ 2) z := by
    unfold auxiliary realCauchy
    simp only [mul_inv_rev]
    ring
  rw [heq]
  have hi := realCauchy_im_eq_poissonExtension ((height_continuous hφ).pow 2)
    (fun s hs => by rw [height_zero_of_one_le_abs φ hs]; norm_num) hz
  simp only [Complex.mul_im]
  norm_num
  rw [hi]
  ring

/-- The actual physical candidate is the exact Poisson variance of its
boundary height, before any H¹₀ or weak equation identification. -/
theorem physicalCandidate_cauchy_eq_poisson_variance {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    physicalCandidate φ (cauchy φ z) =
      (∫ t : ℝ, poissonDensity t *
        (height φ (z.re + z.im * t) - poissonExtension (height φ) z) ^ 2) / 2 := by
  have hF : (cauchy φ z).im = poissonExtension (height φ) z :=
    realCauchy_im_eq_poissonExtension (height_continuous hφ.continuousOn)
      (fun s hs => height_zero_of_one_le_abs φ hs) hz
  simp only [physicalCandidate, PhysicalTorsion.candidate,
    physicalHolomorphic_cauchy hφ hodd hzero hpos hz]
  rw [hF, auxiliary_im_eq_half_poissonExtension hφ.continuousOn hz]
  rw [← poissonExtension_variance (height_continuous hφ.continuousOn)
    (fun s hs => height_zero_of_one_le_abs φ hs) z]
  ring

/-- The actual Poisson variance is strictly positive at every point in H.
At a parameter outside the compact support, its continuous nonnegative
integrand equals the positive Poisson density times the squared positive
mean; a nonempty open set therefore has positive contribution. -/
theorem height_poisson_variance_pos {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    0 < ∫ t : ℝ, poissonDensity t *
      (height φ (z.re + z.im * t) - poissonExtension (height φ) z) ^ 2 := by
  let m := poissonExtension (height φ) z
  have hF : (cauchy φ z).im = m :=
    realCauchy_im_eq_poissonExtension (height_continuous hφ)
      (fun s hs => height_zero_of_one_le_abs φ hs) hz
  have hm : 0 < m := hF ▸ cauchy_im_pos hφ hpos hz
  have hcont : Continuous (fun t : ℝ => poissonDensity t *
      (height φ (z.re + z.im * t) - m) ^ 2) :=
    poissonDensity_continuous.mul ((((height_continuous hφ).comp
      (continuous_const.add (continuous_const.mul continuous_id))).sub continuous_const).pow 2)
  have hint := poissonExtension_variance_integrable (height_continuous hφ)
    (fun s hs => height_zero_of_one_le_abs φ hs) z
  apply integral_pos_of_integrable_nonneg_nonzero (x := (2 + |z.re|) / z.im) hcont hint
    (fun t => mul_nonneg (poissonDensity_nonneg t) (sq_nonneg _))
  let t₀ : ℝ := (2 + |z.re|) / z.im
  have hy : 0 < z.im := hz
  have hcalc : z.re + z.im * t₀ = z.re + 2 + |z.re| := by
    dsimp [t₀]
    field_simp [hy.ne']
    ring
  have hout : 1 ≤ |z.re + z.im * t₀| := by
    rw [hcalc]
    apply le_trans (show 1 ≤ z.re + 2 + |z.re| by linarith [neg_le_abs z.re])
    exact le_abs_self _
  change poissonDensity t₀ * (height φ (z.re + z.im * t₀) - m) ^ 2 ≠ 0
  rw [height_zero_of_one_le_abs φ hout, zero_sub]
  exact (mul_pos (poissonDensity_pos t₀) (sq_pos_of_ne_zero (neg_ne_zero.mpr hm.ne'))).ne'

/-- Strict positivity of the actual classical candidate throughout its
constructed conformal image.  It follows from the exact variance formula,
without assuming a weak solution or invoking a maximum principle. -/
theorem physicalCandidate_pos_on_cauchyImage {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ cauchyImage φ) : 0 < physicalCandidate φ w := by
  obtain ⟨z, hz, rfl⟩ := hw
  rw [physicalCandidate_cauchy_eq_poisson_variance hφ hodd hzero hpos hz]
  exact div_pos (height_poisson_variance_pos hφ.continuousOn hpos hz) (by norm_num)

end Torsion.Spectral

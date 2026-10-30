import Torsion.PhysicalCauchyGreen
import Torsion.PositiveLocalInverse

/-!
# The physical inward-normal Green source at the marked point

Odd profile symmetry makes the infinity chart preserve the imaginary axis.
Its actual positive scalar derivative gives a local real inverse of the
physical height. This turns the already normalized chart-source quotient
into the quotient along the straight physical inward normal.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace Torsion.Spectral

/-- The actual infinity chart maps the positive imaginary axis into itself. -/
theorem cauchyAtInfinity_imaginaryAxis_re {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {t : ℝ} (ht : 0 < t) :
    (cauchyAtInfinity φ ((t : Plane) * Complex.I)).re = 0 := by
  have htC : (t : Plane) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') Complex.I_ne_zero
  have hcoord : -((t : Plane) * Complex.I)⁻¹ = (t⁻¹ : ℝ) * Complex.I := by
    simp [mul_inv_rev, Complex.inv_I, mul_comm]
  rw [cauchyAtInfinity_eq htC, hcoord]
  apply cauchy_re_zero_of_re_zero hφ hodd hzero
  · simpa [upperHalfPlane] using inv_pos.mpr ht
  · simp

/-- The physical height in the marked chart has the strict derivative
`M/π`, proved from the actual complex derivative at infinity. -/
theorem cauchyAtInfinity_axisHeight_hasStrictDerivAt_zero {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    HasStrictDerivAt
      (fun t : ℝ => (cauchyAtInfinity φ ((t : Plane) * Complex.I)).im)
      (mass φ / Real.pi) 0 := by
  have hi : HasStrictDerivAt (fun z : Plane => z * Complex.I) Complex.I 0 := by
    simpa using (hasStrictDerivAt_id (0 : Plane)).mul_const Complex.I
  have hF : HasStrictDerivAt (cauchyAtInfinity φ)
      ((Real.pi : Plane)⁻¹ * (mass φ : Plane)) ((0 : Plane) * Complex.I) := by
    simpa using cauchyAtInfinity_hasStrictDerivAt_zero hφ
  have h := (((hF.comp 0 hi).const_mul (-Complex.I)).real_of_complex)
  convert h using 1
  · funext t
    simp [Complex.mul_re, Complex.mul_im]
  · simp only [← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im]
    ring

/-- At the marked physical boundary point, the normalized Green source
quotient along the straight inward unit normal is the actual marked kernel.
The source points are `(t : ℂ) * I`, not merely a curve tangent to that normal. -/
theorem physicalGreen_marked_normal_source_tendsto {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ cauchyImage φ) :
    Tendsto (fun t : ℝ => physicalGreen φ w ((t : Plane) * Complex.I) / t)
      (𝓝[>] 0) (𝓝 (physicalMarkedKernel φ w)) := by
  obtain ⟨τ, _, _, hτ, hright⟩ := Torsion.exists_positive_local_inverse
    (cauchyAtInfinity_axisHeight_hasStrictDerivAt_zero hφ.continuousOn)
    (by simp) (div_pos (mass_pos hφ.continuousOn hpos) Real.pi_pos)
  have h := (physicalGreen_marked_source_quotient_tendsto hφ hodd hzero hpos hw).comp hτ
  apply h.congr'
  have hτpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < τ t :=
    hτ.eventually self_mem_nhdsWithin
  filter_upwards [hτpos, hright.filter_mono nhdsWithin_le_nhds] with t ht hright
  have heq : cauchyAtInfinity φ ((τ t : Plane) * Complex.I) = (t : Plane) * Complex.I := by
    apply Complex.ext
    · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero] using
        cauchyAtInfinity_imaginaryAxis_re hφ hodd hzero ht
    · simpa using hright
  simp only [Function.comp_apply]
  rw [heq]
  simp

/-- The straight inward normal source points really lie in the actual
Cauchy image for every sufficiently small positive physical distance. -/
theorem eventually_imaginaryAxis_mem_cauchyImage {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (t : Plane) * Complex.I ∈ cauchyImage φ := by
  obtain ⟨τ, _, _, hτ, hright⟩ := Torsion.exists_positive_local_inverse
    (cauchyAtInfinity_axisHeight_hasStrictDerivAt_zero hφ.continuousOn)
    (by simp) (div_pos (mass_pos hφ.continuousOn hpos) Real.pi_pos)
  have hτpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < τ t :=
    hτ.eventually self_mem_nhdsWithin
  filter_upwards [hτpos, hright.filter_mono nhdsWithin_le_nhds] with t ht hright
  have heq : cauchyAtInfinity φ ((τ t : Plane) * Complex.I) = (t : Plane) * Complex.I := by
    apply Complex.ext
    · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero] using
        cauchyAtInfinity_imaginaryAxis_re hφ hodd hzero ht
    · simpa using hright
  rw [← heq, cauchyAtInfinity_eq
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') Complex.I_ne_zero)]
  apply mem_image_of_mem
  change 0 < (-((τ t : Plane) * Complex.I)⁻¹).im
  have hcoord : -((τ t : Plane) * Complex.I)⁻¹ = ((τ t)⁻¹ : ℝ) * Complex.I := by
    simp [mul_inv_rev, Complex.inv_I, mul_comm]
  rw [hcoord]
  simpa using inv_pos.mpr ht

/-- The one-sided physical unit-normal source derivative of the Green
function, with its proved zero boundary value adjoined, is the marked
Poisson kernel. -/
theorem physicalGreen_marked_normal_source_hasDerivWithinAt {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ cauchyImage φ) :
    HasDerivWithinAt
      (fun t : ℝ => if t = 0 then 0 else physicalGreen φ w ((t : Plane) * Complex.I))
      (physicalMarkedKernel φ w) (Ici 0) 0 := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have hset : (Ici (0 : ℝ) \ {0}) = Ioi 0 := by
    ext t
    simp only [mem_diff, mem_Ici, mem_singleton_iff, mem_Ioi]
    constructor
    · rintro ⟨ht, hne⟩
      exact lt_of_le_of_ne ht (Ne.symm hne)
    · intro ht
      exact ⟨ht.le, ht.ne'⟩
  rw [hset]
  apply (physicalGreen_marked_normal_source_tendsto hφ hodd hzero hpos hw).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  simp [slope_def_field, htpos.ne']

end Torsion.Spectral

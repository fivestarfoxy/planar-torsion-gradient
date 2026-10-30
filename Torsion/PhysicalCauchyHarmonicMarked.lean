module

public import Torsion.PhysicalCauchyHarmonicLift

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Exact marked action of the actual compact-data harmonic lift

The first moment of the genuine Cauchy integral gives its derivative at
infinity. Dividing by the physical chart derivative and using its actual
positive scalar inverse yields the straight inward-normal derivative of
the harmonic lift, with normalization `(∫ g)/M`.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Torsion.Spectral

/-- The real-density Cauchy integral in the filled infinity coordinate. -/
def realCauchyAtInfinity (g : ℝ → ℝ) (w : Plane) : Plane :=
  if w = 0 then 0 else realCauchy g (-w⁻¹)

@[simp] theorem realCauchyAtInfinity_zero (g : ℝ → ℝ) : realCauchyAtInfinity g 0 = 0 := by
  simp [realCauchyAtInfinity]

theorem realCauchyAtInfinity_eq (g : ℝ → ℝ) {w : Plane} (hw : w ≠ 0) :
    realCauchyAtInfinity g w = realCauchy g (-w⁻¹) := by
  simp [realCauchyAtInfinity, hw]

/-- The exact coefficient at infinity for arbitrary continuous real data. -/
theorem realCauchy_first_moment {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) {A : Type*} {l : Filter A} {z : A → Plane}
    (hz : Tendsto (fun a => ‖z a‖) l atTop) :
    Tendsto (fun a => z a * realCauchy g (z a)) l
      (𝓝 (-((Real.pi : Plane)⁻¹) * ((∫ s in Icc (-1 : ℝ) 1, g s : ℝ) : Plane))) := by
  have h := (cauchy_integral_first_moment
    (Complex.continuous_ofReal.comp_continuousOn hg) hz).const_mul (-((Real.pi : Plane)⁻¹))
  simp only [Function.comp_apply, integral_complex_ofReal] at h
  convert h using 1
  funext a
  dsimp [realCauchy]
  ring

theorem realCauchyAtInfinity_hasDerivAt_zero {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) :
    HasDerivAt (realCauchyAtInfinity g)
      ((Real.pi : Plane)⁻¹ * ((∫ s in Icc (-1 : ℝ) 1, g s : ℝ) : Plane)) 0 := by
  have hnorm : Tendsto (fun w : Plane => ‖-w⁻¹‖) (𝓝[≠] 0) atTop := by
    simpa only [norm_neg] using (NormedField.tendsto_norm_inv_nhdsNE_zero_atTop (α := Plane))
  have hm := (realCauchy_first_moment hg hnorm).neg
  apply hasDerivAt_iff_tendsto_slope_zero.2
  have heq : (fun w : Plane => w⁻¹ • (realCauchyAtInfinity g (0 + w) - realCauchyAtInfinity g 0))
      =ᶠ[𝓝[≠] 0] (fun w : Plane => -((-w⁻¹) * realCauchy g (-w⁻¹))) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : w ≠ 0 := by simpa using hw
    simp [realCauchyAtInfinity_eq g hw', smul_eq_mul]
  simpa only [neg_mul, neg_neg] using hm.congr' heq.symm

theorem realCauchyAtInfinity_axisHeight_hasDerivAt_zero {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) :
    HasDerivAt (fun t : ℝ => (realCauchyAtInfinity g ((t : Plane) * Complex.I)).im)
      ((∫ s in Icc (-1 : ℝ) 1, g s) / Real.pi) 0 := by
  have hi : HasDerivAt (fun z : Plane => z * Complex.I) Complex.I 0 := by
    simpa using (hasDerivAt_id (0 : Plane)).mul_const Complex.I
  have hF : HasDerivAt (realCauchyAtInfinity g)
      ((Real.pi : Plane)⁻¹ * ((∫ s in Icc (-1 : ℝ) 1, g s : ℝ) : Plane)) ((0 : Plane) * Complex.I) := by
    simpa only [zero_mul] using realCauchyAtInfinity_hasDerivAt_zero hg
  have h := (((hF.comp 0 hi).const_mul (-Complex.I)).real_of_complex)
  convert h using 1
  · funext t
    simp [Complex.mul_re, Complex.mul_im]
  · simp only [← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im]
    ring

/-- In the infinity chart, the marked quotient of the actual harmonic lift
has precisely the density integral divided by the actual profile mass. -/
theorem physicalHarmonicLift_marked_chart_quotient_tendsto {φ g : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) :
    Tendsto (fun t : ℝ => physicalHarmonicLift φ g
      (cauchyAtInfinity φ ((t : Plane) * Complex.I)) /
        (cauchyAtInfinity φ ((t : Plane) * Complex.I)).im)
      (𝓝[>] 0) (𝓝 ((∫ s in Icc (-1 : ℝ) 1, g s) / mass φ)) := by
  have hnum : Tendsto (fun t : ℝ =>
      (realCauchyAtInfinity g ((t : Plane) * Complex.I)).im / t)
      (𝓝[>] 0) (𝓝 ((∫ s in Icc (-1 : ℝ) 1, g s) / Real.pi)) := by
    simpa only [zero_add, Complex.ofReal_zero, zero_mul, mul_zero, realCauchyAtInfinity_zero,
      Complex.zero_im, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (realCauchyAtInfinity_axisHeight_hasDerivAt_zero hg).tendsto_slope_zero_right
  have hden : Tendsto (fun t : ℝ =>
      (cauchyAtInfinity φ ((t : Plane) * Complex.I)).im / t)
      (𝓝[>] 0) (𝓝 (mass φ / Real.pi)) := by
    simpa only [zero_add, Complex.ofReal_zero, zero_mul, mul_zero, cauchyAtInfinity_zero,
      Complex.zero_im, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (cauchyAtInfinity_axisHeight_hasStrictDerivAt_zero hφ.continuousOn).hasDerivAt.tendsto_slope_zero_right
  have hM := (mass_pos hφ.continuousOn hpos).ne'
  have hlim := hnum.div hden (div_ne_zero hM Real.pi_ne_zero)
  have hvalue : ((∫ s in Icc (-1 : ℝ) 1, g s) / Real.pi) / (mass φ / Real.pi) =
      (∫ s in Icc (-1 : ℝ) 1, g s) / mass φ := by field_simp
  rw [hvalue] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have htC : (t : Plane) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne') Complex.I_ne_zero
  have hz : -((t : Plane) * Complex.I)⁻¹ ∈ upperHalfPlane := by
    have he : -((t : Plane) * Complex.I)⁻¹ = (t⁻¹ : ℝ) * Complex.I := by
      simp [mul_inv_rev, Complex.inv_I, mul_comm]
    rw [he]
    simpa [upperHalfPlane] using inv_pos.mpr htpos
  change ((realCauchyAtInfinity g ((t : Plane) * Complex.I)).im / t) /
    ((cauchyAtInfinity φ ((t : Plane) * Complex.I)).im / t) = _
  rw [realCauchyAtInfinity_eq g htC, cauchyAtInfinity_eq htC,
    physicalHarmonicLift_cauchy hφ hodd hzero hpos g hz]
  exact div_div_div_cancel_right₀ htpos.ne' _ _

/-- The marked action is the actual straight physical inward-normal
derivative, rather than a quotient along a merely tangent chart curve. -/
theorem physicalHarmonicLift_marked_normal_tendsto {φ g : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) :
    Tendsto (fun t : ℝ => physicalHarmonicLift φ g ((t : Plane) * Complex.I) / t)
      (𝓝[>] 0) (𝓝 ((∫ s in Icc (-1 : ℝ) 1, g s) / mass φ)) := by
  obtain ⟨τ, _, _, hτ, hright⟩ := Torsion.exists_positive_local_inverse
    (cauchyAtInfinity_axisHeight_hasStrictDerivAt_zero hφ.continuousOn)
    (by simp) (div_pos (mass_pos hφ.continuousOn hpos) Real.pi_pos)
  have h := (physicalHarmonicLift_marked_chart_quotient_tendsto
    hφ hodd hzero hpos hg).comp hτ
  apply h.congr'
  have hτpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < τ t := hτ.eventually self_mem_nhdsWithin
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

/-- The marked-flux relation uses the original physical straight inward
normal and its actual limiting quotient. -/
theorem physicalHarmonicLift_hasMarkedFlux {φ g : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) :
    HasMarkedFlux (physicalHarmonicLift φ g) ((∫ s in Icc (-1 : ℝ) 1, g s) / mass φ) :=
  physicalHarmonicLift_marked_normal_tendsto hφ hodd hzero hpos hg

/-- After adjoining its zero value at the marked boundary, the actual lift
has the indicated one-sided normal derivative, including the endpoint. -/
theorem physicalHarmonicLift_marked_normal_hasDerivWithinAt {φ g : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) :
    HasDerivWithinAt
      (fun t : ℝ => if t = 0 then 0 else physicalHarmonicLift φ g ((t : Plane) * Complex.I))
      ((∫ s in Icc (-1 : ℝ) 1, g s) / mass φ) (Ici 0) 0 := by
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
  apply (physicalHarmonicLift_marked_normal_tendsto hφ hodd hzero hpos hg).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  simp [slope_def_field, htpos.ne']

end Torsion.Spectral

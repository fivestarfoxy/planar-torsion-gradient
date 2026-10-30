import Torsion.CauchyConformalGeometry.BoundaryCurvature

/-!
# Hölder regularity of the actual closed free arc

On the free interval the linear Hilbert equation identifies the real
component of the actual tangent with `b - a Y`.  Thus the Hölder regularity
of that tangent follows directly from the profile and the proved primitive
calculus.  No Hölder theorem for a general Hilbert transform is assumed.
This concerns the closed free arc, not yet the whole compactified boundary.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The zero-exterior Hölder estimate supplies the endpoint vanishing rate
of the original profile, with its actual Hölder constant. -/
theorem profile_endpoint_bound {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖φ x‖ ≤ (C : ℝ) * (1 - x) ^ (α : ℝ) := by
  have h := hφ.dist_le x 1
  rw [hzero 1 (by norm_num), dist_zero_right] at h
  simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.2), neg_sub] using h

/-- Integrating the actual endpoint Hölder bound gives the extra power of
vanishing for the height.  At exponent one half this is the required
`(1-|x|)^(3/2)` bound; the harmless constant is the original Hölder constant. -/
theorem height_endpoint_bound {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {x : ℝ} (hx : |x| ≤ 1) :
    ‖height φ x‖ ≤ (C : ℝ) * (1 - |x|) ^ ((α : ℝ) + 1) := by
  by_cases hxe : |x| = 1
  · rw [height_zero_of_one_le_abs φ hxe.ge, hxe]
    simp [Real.zero_rpow (by positivity : (α : ℝ) + 1 ≠ 0)]
  have hxl : |x| < 1 := lt_of_le_of_ne hx hxe
  rw [height, if_pos hxl]
  have hbound : ∀ s ∈ Icc |x| 1,
      ‖φ s‖ ≤ (C : ℝ) * (1 - |x|) ^ (α : ℝ) := by
    intro s hs
    exact (profile_endpoint_bound hφ hzero ⟨(abs_nonneg x).trans hs.1, hs.2⟩).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (sub_nonneg.mpr hs.2) (by linarith [hs.1]) α.coe_nonneg)
        C.coe_nonneg)
  have hb := norm_setIntegral_le_of_norm_le_const
    (s := Icc |x| 1) (μ := volume) isCompact_Icc.measure_lt_top hbound
  calc
    ‖∫ s in Icc |x| 1, φ s‖ ≤
        (C : ℝ) * (1 - |x|) ^ (α : ℝ) * (volume (Icc |x| 1)).toReal := hb
    _ = (C : ℝ) * (1 - |x|) ^ ((α : ℝ) + 1) := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hx),
        Real.rpow_add (sub_pos.mpr hxl), Real.rpow_one]
      ring

/-- The actual closed free-arc tangent inherits the profile's Hölder
exponent.  This includes both junctions with the flat side. -/
theorem cauchy_boundary_tangent_holderOn {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    ∃ K : ℝ≥0, HolderOnWith K α
      (fun x : ℝ => cauchyDerivativeExtension φ (x : ℂ)) (Icc (-1 : ℝ) 1) := by
  obtain ⟨D, hY⟩ := height_exists_holder (hφ.continuous hα0) hodd hzero hα1
  let K : ℝ≥0 := ⟨|a|, abs_nonneg a⟩ * D + C
  refine ⟨K, ?_⟩
  intro x hx y hy
  have hdist : dist (cauchyDerivativeExtension φ (x : ℂ))
      (cauchyDerivativeExtension φ (y : ℂ)) ≤
      (K : ℝ) * dist x y ^ (α : ℝ) := by
    rw [cauchy_boundary_tangent_eq hφ hα0 hzero hlinear hx,
      cauchy_boundary_tangent_eq hφ hα0 hzero hlinear hy]
    have hsplit :
        ((boundaryVelocity a b φ x : ℂ) - (φ x : ℂ) * Complex.I) -
          ((boundaryVelocity a b φ y : ℂ) - (φ y : ℂ) * Complex.I) =
        ((-a * (height φ x - height φ y) : ℝ) : ℂ) -
          ((φ x - φ y : ℝ) : ℂ) * Complex.I := by
      simp only [boundaryVelocity]
      push_cast
      ring
    rw [dist_eq_norm, hsplit]
    calc
      ‖((-a * (height φ x - height φ y) : ℝ) : ℂ) -
          ((φ x - φ y : ℝ) : ℂ) * Complex.I‖ ≤
          |a| * dist (height φ x) (height φ y) + dist (φ x) (φ y) := by
        simpa only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
          norm_mul, Complex.norm_I, mul_one, Real.dist_eq] using
          norm_sub_le (((-a * (height φ x - height φ y) : ℝ) : ℂ))
            (((φ x - φ y : ℝ) : ℂ) * Complex.I)
      _ ≤ |a| * ((D : ℝ) * dist x y ^ (α : ℝ)) +
          (C : ℝ) * dist x y ^ (α : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left (hY.dist_le x y) (abs_nonneg a))
          (hφ.dist_le x y)
      _ = (K : ℝ) * dist x y ^ (α : ℝ) := by
        simp only [K, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk]
        ring
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal hdist

/-- In particular the derivative of the genuine C¹ boundary
parametrization is Hölder on the closed free interval. -/
theorem cauchy_boundary_deriv_holderOn {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    ∃ K : ℝ≥0, HolderOnWith K α
      (deriv (fun x : ℝ => cauchyExtension φ (x : ℂ))) (Icc (-1 : ℝ) 1) := by
  have heq : deriv (fun x : ℝ => cauchyExtension φ (x : ℂ)) =
      fun x : ℝ => cauchyDerivativeExtension φ (x : ℂ) :=
    funext fun x => (cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero x).deriv
  rw [heq]
  exact cauchy_boundary_tangent_holderOn hφ hα0 hα1 hodd hzero hlinear

end Torsion.Spectral

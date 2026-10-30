import Torsion.CauchyConformalGeometry.Convexity
import Torsion.CauchyConformalGeometry.InverseBoundary
import Torsion.PhysicalCauchyKernel

/-!
# Genuine supporting unit normals and signed boundary stationarity

The normal is constructed from the actual boundary tangent. Its unit length,
orthogonality and inward supporting direction concern the actual convex
image. The signed limits below use the actual physical torsion and the
concrete positive harmonic marked-kernel candidate. They do not identify
that harmonic function with a Green/Poisson kernel.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The positively rotated, normalized actual free-arc tangent. -/
def cauchyInwardNormal (φ : ℝ → ℝ) (t : ℝ) : ℂ :=
  ‖cauchyDerivativeExtension φ (t : ℂ)‖⁻¹ •
    (Complex.I * cauchyDerivativeExtension φ (t : ℂ))

/-- The opposite, outward supporting normal. -/
def cauchyOutwardNormal (φ : ℝ → ℝ) (t : ℝ) : ℂ := -cauchyInwardNormal φ t

/-- The concrete normalized tangent rotation has unit length. -/
theorem cauchyInwardNormal_norm {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : ‖cauchyInwardNormal φ t‖ = 1 := by
  have hn : ‖cauchyDerivativeExtension φ (t : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2
    (cauchyDerivativeExtension_ne_zero_on_interval ha hφ hα0 hα1 hodd hzero hpos hlinear ht)
  simp [cauchyInwardNormal, norm_smul, norm_mul, Complex.norm_I, Real.norm_eq_abs, hn]

/-- The constructed normal is orthogonal to the actual tangent. -/
theorem cauchyInwardNormal_orthogonal (φ : ℝ → ℝ) (t : ℝ) :
    inner (𝕜 := ℝ) (cauchyInwardNormal φ t)
      (cauchyDerivativeExtension φ (t : ℂ)) = 0 := by
  rw [cauchyInwardNormal, real_inner_smul_left]
  have hrot (z : ℂ) : inner (𝕜 := ℝ) (Complex.I * z) z = 0 := by
    simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add]
    ring
  rw [hrot, mul_zero]

/-- The normal's actual Euclidean supporting expression is the tangent
functional already proved to support the actual free arc. -/
theorem cauchyInwardNormal_support_identity {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (w : ℂ) :
    inner (𝕜 := ℝ) (cauchyInwardNormal φ t) (w - cauchyExtension φ (t : ℂ)) =
      cauchySupport a b φ t w / ‖cauchyDerivativeExtension φ (t : ℂ)‖ := by
  rw [cauchyInwardNormal, real_inner_smul_left]
  have heq : inner (𝕜 := ℝ) (Complex.I * cauchyDerivativeExtension φ (t : ℂ))
      (w - cauchyExtension φ (t : ℂ)) = cauchySupport a b φ t w := by
    rw [cauchy_boundary_tangent_eq hφ hα0 hzero hlinear ht, cauchySupport_eq]
    simp only [Complex.inner, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, mul_one, one_mul,
      zero_sub, sub_zero, add_zero, zero_add, Complex.conj_re, Complex.conj_im]
    simp only [cauchyExtension_ofReal, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add]
    ring
  rw [heq, div_eq_mul_inv, mul_comm]

/-- The actual inward normal supports the entire closure of the image. -/
theorem cauchyInwardNormal_support_closure {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {w : ℂ} (hw : w ∈ closure (cauchyImage φ)) :
    0 ≤ inner (𝕜 := ℝ) (cauchyInwardNormal φ t) (w - cauchyExtension φ (t : ℂ)) := by
  let ℓ := cauchySupportFunctional a b φ t
  have hne : ℓ ≠ 0 := cauchySupportFunctional_ne_zero ha hφ hα0 hα1 hodd hzero hpos hlinear ht
  have hbound : ∀ q ∈ frontier (cauchyImage φ), (-ℓ) q ≤ (-ℓ) (cauchyExtension φ (t : ℂ)) := by
    intro q hq
    have hq' := sub_nonneg.1 (cauchySupport_nonneg_frontier
      ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd ht hq)
    exact neg_le_neg hq'
  have hle := linearFunctional_le_closure_of_frontier_le
    (cauchyImage_isOpen (hφ.continuous hα0) hodd hzero hpos)
    (cauchy_image_isBounded (hφ.continuous hα0) hodd hzero)
    (-ℓ) (neg_ne_zero.mpr hne) hbound hw
  rw [cauchyInwardNormal_support_identity hφ hα0 hzero hlinear ht]
  apply div_nonneg _ (norm_nonneg _)
  exact sub_nonneg.2 (neg_le_neg_iff.1 hle)

/-- Every interior point lies strictly on the inward side of this actual
supporting tangent line. -/
theorem cauchyInwardNormal_support_interior {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {w : ℂ} (hw : w ∈ cauchyImage φ) :
    0 < inner (𝕜 := ℝ) (cauchyInwardNormal φ t) (w - cauchyExtension φ (t : ℂ)) := by
  let ℓ := cauchySupportFunctional a b φ t
  have hne : ℓ ≠ 0 := cauchySupportFunctional_ne_zero ha hφ hα0 hα1 hodd hzero hpos hlinear ht
  have hbound : ∀ q ∈ cauchyImage φ, (-ℓ) q ≤ (-ℓ) (cauchyExtension φ (t : ℂ)) := by
    intro q hq
    have hq' := cauchyInwardNormal_support_closure
      ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd ht (subset_closure hq)
    rw [cauchyInwardNormal_support_identity hφ hα0 hzero hlinear ht] at hq'
    have hn : 0 < ‖cauchyDerivativeExtension φ (t : ℂ)‖ := norm_pos_iff.2
      (cauchyDerivativeExtension_ne_zero_on_interval ha hφ hα0 hα1 hodd hzero hpos hlinear ht)
    have hsup : 0 ≤ cauchySupport a b φ t q := by
      simpa using (le_div_iff₀ hn).1 hq'
    exact neg_le_neg (sub_nonneg.1 hsup)
  have hlt := linearFunctional_lt_on_open_of_le
    (cauchyImage_isOpen (hφ.continuous hα0) hodd hzero hpos) (-ℓ) (neg_ne_zero.mpr hne) hbound hw
  rw [cauchyInwardNormal_support_identity hφ hα0 hzero hlinear ht]
  exact div_pos (sub_pos.2 (neg_lt_neg_iff.1 hlt))
    (norm_pos_iff.2 (cauchyDerivativeExtension_ne_zero_on_interval
      ha hφ hα0 hα1 hodd hzero hpos hlinear ht))


/-- The exact limiting physical torsion gradient points in the genuine
inward unit normal direction. -/
theorem gradient_physicalCandidate_boundary_normal_tendsto
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun z => gradient (physicalCandidate φ) (cauchy φ z))
      (𝓝[upperHalfPlane] (t : Plane))
      (𝓝 ((‖cauchyDerivativeExtension φ (t : Plane)‖ / (2 * a)) • cauchyInwardNormal φ t)) := by
  have hn := norm_ne_zero_iff.2
    (cauchyDerivativeExtension_ne_zero_on_interval ha hφ hα0 hα1 hodd hzero hpos hlinear ht)
  have h := gradient_physicalCandidate_cauchy_boundary_tendsto ha.ne' hφ hα0 hα1 hodd hzero hpos hlinear ht
  have heq : (‖cauchyDerivativeExtension φ (t : Plane)‖ / (2 * a)) • cauchyInwardNormal φ t =
      Complex.I * cauchyDerivativeExtension φ (t : Plane) / ((2 * a : ℝ) : ℂ) := by
    rw [cauchyInwardNormal, smul_smul]
    have hcoeff : ‖cauchyDerivativeExtension φ (t : Plane)‖ / (2 * a) *
        ‖cauchyDerivativeExtension φ (t : Plane)‖⁻¹ = (2 * a)⁻¹ := by
      calc
        _ = (‖cauchyDerivativeExtension φ (t : Plane)‖ *
            ‖cauchyDerivativeExtension φ (t : Plane)‖⁻¹) / (2 * a) := by ring
        _ = (2 * a)⁻¹ := by rw [mul_inv_cancel₀ hn]; simp [one_div]
    rw [hcoeff, Complex.real_smul, Complex.ofReal_inv]
    simp only [div_eq_mul_inv, mul_comm]
  rwa [heq]

/-- The concrete harmonic candidate's gradient has the same actual inward
normal direction, with reciprocal conformal speed. -/
theorem physicalMarkedKernel_boundaryGradient_eq_normal (φ : ℝ → ℝ) (t : ℝ) :
    (mass φ)⁻¹ • (Complex.I * star (cauchyDerivativeExtension φ (t : Plane))⁻¹) =
      (1 / (mass φ * ‖cauchyDerivativeExtension φ (t : Plane)‖)) • cauchyInwardNormal φ t := by
  have hstar (z : ℂ) : star z⁻¹ = (‖z‖ ^ 2)⁻¹ • z := by
    simp only [Complex.star_def, Complex.inv_def, map_mul, Complex.conj_conj,
      Complex.conj_ofReal, Complex.normSq_eq_norm_sq, Complex.real_smul]
    ring
  rw [hstar, mul_smul_comm, smul_smul, cauchyInwardNormal, smul_smul]
  congr 1
  simp only [div_eq_mul_inv, one_mul, pow_two, mul_inv_rev]
  ring

/-- Arbitrary interior parameter approach gives the exact vector normal
limit for the concrete harmonic marked-kernel candidate. -/
theorem gradient_physicalMarkedKernel_boundary_normal_tendsto
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun z => gradient (physicalMarkedKernel φ) (cauchy φ z))
      (𝓝[upperHalfPlane] (t : Plane))
      (𝓝 ((1 / (mass φ * ‖cauchyDerivativeExtension φ (t : Plane)‖)) • cauchyInwardNormal φ t)) := by
  have h := gradient_physicalMarkedKernel_cauchy_boundary_tendsto ha hφ hα0 hα1 hodd hzero hpos hlinear ht
  rwa [physicalMarkedKernel_boundaryGradient_eq_normal] at h

/-- The negative outward-normal torsion gradient has the exact positive
boundary value q=|F'|/(2a), with the normal's orientation already proved. -/
theorem neg_outwardGradient_physicalCandidate_boundary_tendsto
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun z => -inner (𝕜 := ℝ) (gradient (physicalCandidate φ) (cauchy φ z))
      (cauchyOutwardNormal φ t)) (𝓝[upperHalfPlane] (t : Plane))
      (𝓝 (‖cauchyDerivativeExtension φ (t : Plane)‖ / (2 * a))) := by
  have h := (gradient_physicalCandidate_boundary_normal_tendsto
    ha hφ hα0 hα1 hodd hzero hpos hlinear ht).inner
      (tendsto_const_nhds (x := cauchyInwardNormal φ t)) (𝕜 := ℝ)
  have hunit := cauchyInwardNormal_norm ha hφ hα0 hα1 hodd hzero hpos hlinear ht
  simpa only [cauchyOutwardNormal, inner_neg_right, neg_neg, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hunit, one_pow, mul_one] using h

/-- The concrete harmonic candidate has positive negative outward-normal
value k=1/(M|F'|) along the free arc. -/
theorem neg_outwardGradient_physicalMarkedKernel_boundary_tendsto
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun z => -inner (𝕜 := ℝ) (gradient (physicalMarkedKernel φ) (cauchy φ z))
      (cauchyOutwardNormal φ t)) (𝓝[upperHalfPlane] (t : Plane))
      (𝓝 (1 / (mass φ * ‖cauchyDerivativeExtension φ (t : Plane)‖))) := by
  have h := (gradient_physicalMarkedKernel_boundary_normal_tendsto
    ha hφ hα0 hα1 hodd hzero hpos hlinear ht).inner
      (tendsto_const_nhds (x := cauchyInwardNormal φ t)) (𝕜 := ℝ)
  have hunit := cauchyInwardNormal_norm ha hφ hα0 hα1 hodd hzero hpos hlinear ht
  simpa only [cauchyOutwardNormal, inner_neg_right, neg_neg, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hunit, one_pow, mul_one] using h

/-- The product of the two genuine signed normal-gradient limits is the
constant stationarity factor 1/(2aM). The kernel here remains the concrete
harmonic candidate, without a Green/Poisson identification. -/
theorem signed_stationarity_physicalCandidate_kernel_boundary_tendsto
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun z =>
      (-inner (𝕜 := ℝ) (gradient (physicalCandidate φ) (cauchy φ z)) (cauchyOutwardNormal φ t)) *
      (-inner (𝕜 := ℝ) (gradient (physicalMarkedKernel φ) (cauchy φ z)) (cauchyOutwardNormal φ t)))
      (𝓝[upperHalfPlane] (t : Plane)) (𝓝 (1 / (2 * a * mass φ))) := by
  have h := (neg_outwardGradient_physicalCandidate_boundary_tendsto
    ha hφ hα0 hα1 hodd hzero hpos hlinear ht).mul
    (neg_outwardGradient_physicalMarkedKernel_boundary_tendsto
      ha hφ hα0 hα1 hodd hzero hpos hlinear ht)
  have hn := norm_ne_zero_iff.2
    (cauchyDerivativeExtension_ne_zero_on_interval ha hφ hα0 hα1 hodd hzero hpos hlinear ht)
  have hM := (mass_pos (hφ.continuous hα0).continuousOn hpos).ne'
  convert h using 1
  field_simp [ha.ne', hn, hM]
  ring


/-- The actual physical torsion gradient has the genuine inward-normal
limit along every physical interior approach to a free-arc point. -/
theorem gradient_physicalCandidate_tendsto_at_freeArc
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (gradient (physicalCandidate φ))
      (𝓝[cauchyImage φ] (cauchyExtension φ (t : ℂ)))
      (𝓝 ((‖cauchyDerivativeExtension φ (t : Plane)‖ / (2 * a)) • cauchyInwardNormal φ t)) :=
  tendsto_physical_boundary_of_cauchy_comp hφ hα0 hα1 hodd hzero hpos t
    (gradient_physicalCandidate_boundary_normal_tendsto
      ha hφ hα0 hα1 hodd hzero hpos hlinear ht)


/-- The concrete harmonic kernel candidate has the normal vector limit
along every physical interior approach to a free-arc point. -/
theorem gradient_physicalMarkedKernel_tendsto_at_freeArc
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (gradient (physicalMarkedKernel φ))
      (𝓝[cauchyImage φ] (cauchyExtension φ (t : ℂ)))
      (𝓝 ((1 / (mass φ * ‖cauchyDerivativeExtension φ (t : Plane)‖)) • cauchyInwardNormal φ t)) :=
  tendsto_physical_boundary_of_cauchy_comp hφ hα0 hα1 hodd hzero hpos t
    (gradient_physicalMarkedKernel_boundary_normal_tendsto
      ha hφ hα0 hα1 hodd hzero hpos hlinear ht)


/-- The actual negative outward-normal torsion derivative is the trace
q=|F'|/(2a) for arbitrary physical interior approach. -/
theorem neg_outwardGradient_physicalCandidate_tendsto_at_freeArc
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun w => -inner (𝕜 := ℝ) (gradient (physicalCandidate φ) w) (cauchyOutwardNormal φ t))
      (𝓝[cauchyImage φ] (cauchyExtension φ (t : ℂ)))
      (𝓝 (‖cauchyDerivativeExtension φ (t : Plane)‖ / (2 * a))) :=
  tendsto_physical_boundary_of_cauchy_comp hφ hα0 hα1 hodd hzero hpos t
    (neg_outwardGradient_physicalCandidate_boundary_tendsto
      ha hφ hα0 hα1 hodd hzero hpos hlinear ht)


/-- The concrete harmonic candidate has signed normal trace
k=1/(M|F'|) along arbitrary physical interior approach. -/
theorem neg_outwardGradient_physicalMarkedKernel_tendsto_at_freeArc
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun w => -inner (𝕜 := ℝ) (gradient (physicalMarkedKernel φ) w) (cauchyOutwardNormal φ t))
      (𝓝[cauchyImage φ] (cauchyExtension φ (t : ℂ)))
      (𝓝 (1 / (mass φ * ‖cauchyDerivativeExtension φ (t : Plane)‖))) :=
  tendsto_physical_boundary_of_cauchy_comp hφ hα0 hα1 hodd hzero hpos t
    (neg_outwardGradient_physicalMarkedKernel_boundary_tendsto
      ha hφ hα0 hα1 hodd hzero hpos hlinear ht)


/-- The genuine signed-normal stationarity product has constant trace
1/(2aM) along every physical interior approach. The kernel is the concrete
harmonic candidate; Green/Poisson identification is a separate theorem. -/
theorem signed_stationarity_physicalCandidate_kernel_tendsto_at_freeArc
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun w =>
      (-inner (𝕜 := ℝ) (gradient (physicalCandidate φ) w) (cauchyOutwardNormal φ t)) *
      (-inner (𝕜 := ℝ) (gradient (physicalMarkedKernel φ) w) (cauchyOutwardNormal φ t)))
      (𝓝[cauchyImage φ] (cauchyExtension φ (t : ℂ))) (𝓝 (1 / (2 * a * mass φ))) :=
  tendsto_physical_boundary_of_cauchy_comp hφ hα0 hα1 hodd hzero hpos t
    (signed_stationarity_physicalCandidate_kernel_boundary_tendsto
      ha hφ hα0 hα1 hodd hzero hpos hlinear ht)

end Torsion.Spectral

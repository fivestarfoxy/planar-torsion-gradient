import Torsion.CauchyConformalGeometry.BoundaryDerivative
import Torsion.CauchySpectralIdentity

/-! # The signed curvature of the actual free boundary

The scalar curvature estimate is identified here with the tangent and
second derivative of the actual Cauchy boundary parametrization. Thus the
strict sign concerns the constructed curve, not a formally supplied model.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The actual tangent has the velocity/profile decomposition on the
closed free interval, including its support endpoints. -/
theorem cauchy_boundary_tangent_eq {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    cauchyDerivativeExtension φ (x : ℂ) =
      (boundaryVelocity a b φ x : ℂ) - (φ x : ℂ) * Complex.I := by
  apply Complex.ext
  · simpa using cauchyDerivativeExtension_re_eq_boundaryVelocity hφ hα0 hzero hlinear x hx
  · simp [cauchyDerivativeExtension_ofReal]

/-- Differentiating the actual tangent uses the ordinary profile derivative
and the proved velocity ODE. No second-derivative formula is assumed. -/
theorem cauchy_boundary_tangent_hasDerivAt {a b x : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ t ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ t = a * height φ t - b)
    (hd : DifferentiableAt ℝ φ x) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => cauchyDerivativeExtension φ (t : ℂ))
      (((a * φ x : ℝ) : ℂ) - ((deriv φ x : ℝ) : ℂ) * Complex.I) x := by
  have h := (hasDerivAt_boundaryVelocity (a := a) (b := b)
    (hφ.continuous hα0) hodd hzero x).ofReal_comp.sub
      (hd.hasDerivAt.ofReal_comp.mul_const Complex.I)
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  exact cauchy_boundary_tangent_eq hφ hα0 hzero hlinear (Ioo_subset_Icc_self ht)

/-- The standard signed curvature numerator of the actual tangent equals
the scalar expression estimated from concavity. -/
theorem cauchy_boundary_curvature_eq {a b x : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ t ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ t = a * height φ t - b)
    (hd : DifferentiableAt ℝ φ x) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (star (cauchyDerivativeExtension φ (x : ℂ)) *
      deriv (fun t : ℝ => cauchyDerivativeExtension φ (t : ℂ)) x).im =
        a * (φ x) ^ 2 - boundaryVelocity a b φ x * deriv φ x := by
  rw [(cauchy_boundary_tangent_hasDerivAt hφ hα0 hodd hzero hlinear hd hx).deriv,
    cauchy_boundary_tangent_eq hφ hα0 hzero hlinear (Ioo_subset_Icc_self hx)]
  simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_mul, zero_sub, sub_zero, add_zero, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_sub]
  ring

/-- The actual Cauchy free arc has strictly positive signed curvature at
every point of the positive open half-interval. The moment relation,
velocity zero and scalar bounds used to establish this sign are all
derived from the linear Hilbert equation in the imported theorem. -/
theorem cauchy_boundary_curvature_pos {a b x : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ t ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ t = a * height φ t - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ y ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ y)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < (star (cauchyDerivativeExtension φ (x : ℂ)) *
      deriv (fun t : ℝ => cauchyDerivativeExtension φ (t : ℂ)) x).im := by
  rw [cauchy_boundary_curvature_eq hφ hα0 hodd hzero hlinear (hd x hx)
    ⟨by linarith [hx.1], hx.2⟩]
  exact curvature_pos_of_holder_boundary_equation ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd hx

end Torsion.Spectral

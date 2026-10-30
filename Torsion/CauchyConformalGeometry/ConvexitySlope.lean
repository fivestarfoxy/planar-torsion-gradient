module

public import Torsion.CauchyConformalGeometry.BoundaryHolder
public import Torsion.CauchyConformalGeometry.FlatSegment

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Monotonicity of the actual free-arc tangent ratio

The signed curvature estimate is exactly positivity of the derivative of
`boundaryVelocity / φ` on the positive half-interval. This ratio controls
the sign of every derivative of a tangent-line support functional.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The real derivative of the actual boundary parametrization is the
velocity supplied by the linear Hilbert equation, including its endpoints. -/
theorem cauchy_boundary_re_hasDerivAt_velocity {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => (cauchyExtension φ (s : ℂ)).re)
      (boundaryVelocity a b φ x) x := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero x)
  rw [cauchy_boundary_tangent_eq hφ hα0 hzero hlinear hx] at h
  simpa [Function.comp_def, Complex.reCLM_apply] using h

/-- The imaginary derivative of the actual boundary map is `-φ`, as a
consequence of the constructed complex tangent. -/
theorem cauchy_boundary_im_hasDerivAt_profile {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) (x : ℝ) :
    HasDerivAt (fun s : ℝ => (cauchyExtension φ (s : ℂ)).im) (-φ x) x := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x
    (cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero x)
  simpa [Function.comp_def, Complex.imCLM_apply, cauchyDerivativeExtension_ofReal] using h

/-- Curvature positivity makes the actual tangent ratio strictly increasing
on the positive open half of the free arc. -/
theorem boundaryVelocity_div_profile_strictMonoOn {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x) :
    StrictMonoOn (fun x : ℝ => boundaryVelocity a b φ x / φ x) (Ioo (0 : ℝ) 1) := by
  have hderiv (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => boundaryVelocity a b φ x / φ x)
        ((a * (φ x) ^ 2 - boundaryVelocity a b φ x * deriv φ x) / (φ x) ^ 2) x := by
    convert (hasDerivAt_boundaryVelocity (a := a) (b := b)
      (hφ.continuous hα0) hodd hzero x).div (hd x hx).hasDerivAt (hpos x hx).ne' using 1
    ring
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) 1)
    (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
  intro x hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ioo] using hx
  rw [(hderiv x hx').deriv]
  exact div_pos (curvature_pos_of_holder_boundary_equation
    ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd hx')
    (sq_pos_of_pos (hpos x hx'))

end Torsion.Spectral

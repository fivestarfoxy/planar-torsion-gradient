import Torsion.CauchyConformalGeometry.Univalence
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.Conformal

/-! # The actual conformal inverse on the Cauchy image

The inverse is selected from the upper half-plane. Its identities come
from the proved univalence, its derivative from the strict inverse
function theorem, and its holomorphy from the resulting open image.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace Torsion.Spectral

/-- The actual (not yet asserted convex) image of the upper half-plane. -/
def cauchyImage (φ : ℝ → ℝ) : Set ℂ := cauchy φ '' upperHalfPlane

/-- An inverse selected among upper-half-plane preimages. All analytic
properties are proved on `cauchyImage`; exterior values are immaterial. -/
def cauchyInverse (φ : ℝ → ℝ) : ℂ → ℂ :=
  Function.invFunOn (cauchy φ) upperHalfPlane

theorem cauchyInverse_mem {φ : ℝ → ℝ} {w : ℂ} (hw : w ∈ cauchyImage φ) :
    cauchyInverse φ w ∈ upperHalfPlane :=
  Function.invFunOn_mem hw

theorem cauchy_cauchyInverse {φ : ℝ → ℝ} {w : ℂ} (hw : w ∈ cauchyImage φ) :
    cauchy φ (cauchyInverse φ w) = w :=
  Function.invFunOn_eq hw

theorem cauchyInverse_cauchy {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    cauchyInverse φ (cauchy φ z) = z :=
  (cauchy_injOn_upperHalfPlane hφ hodd hzero hpos).leftInvOn_invFunOn hz

theorem cauchy_hasStrictDerivAt {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasStrictDerivAt (cauchy φ) (deriv (cauchy φ) z) z :=
  (cauchy_analyticOnNhd hφ z hz).hasStrictFDerivAt.hasStrictDerivAt

/-- The concrete inverse has the reciprocal complex derivative, by the
strict inverse function theorem and the actual left-inverse identity. -/
theorem cauchyInverse_hasStrictDerivAt {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasStrictDerivAt (cauchyInverse φ) (deriv (cauchy φ) z)⁻¹ (cauchy φ z) := by
  have hH : IsOpen upperHalfPlane := isOpen_lt continuous_const Complex.continuous_im
  apply (cauchy_hasStrictDerivAt hφ.continuousOn hz).to_local_left_inverse
    (cauchy_derivative_ne_zero hφ hodd hzero hpos hz)
  filter_upwards [hH.mem_nhds hz] with w hw
  exact cauchyInverse_cauchy hφ hodd hzero hpos hw

theorem cauchyInverse_hasDerivAt {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasDerivAt (cauchyInverse φ) (deriv (cauchy φ) z)⁻¹ (cauchy φ z) :=
  (cauchyInverse_hasStrictDerivAt hφ hodd hzero hpos hz).hasDerivAt

/-- The Cauchy map is open on every open subset of H. This uses the
nonzero strict derivative, without any boundary mapping theorem. -/
theorem isOpen_cauchy_image {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {S : Set ℂ} (hS : IsOpen S) (hSH : S ⊆ upperHalfPlane) :
    IsOpen (cauchy φ '' S) := by
  apply isOpen_iff_mem_nhds.2
  rintro w ⟨z, hz, rfl⟩
  have hmap := (cauchy_hasStrictDerivAt hφ.continuousOn (hSH hz)).map_nhds_eq
    (cauchy_derivative_ne_zero hφ hodd hzero hpos (hSH hz))
  rw [← hmap]
  exact image_mem_map (hS.mem_nhds hz)

theorem cauchyImage_isOpen {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    IsOpen (cauchyImage φ) :=
  isOpen_cauchy_image hφ hodd hzero hpos
    (isOpen_lt continuous_const Complex.continuous_im) Subset.rfl

theorem cauchyInverse_differentiableOn {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    DifferentiableOn ℂ (cauchyInverse φ) (cauchyImage φ) := by
  rintro w ⟨z, hz, rfl⟩
  exact (cauchyInverse_hasDerivAt hφ hodd hzero hpos hz).differentiableAt.differentiableWithinAt

/-- Holomorphy of the inverse is a consequence of the constructed inverse
and the proved univalence, rather than a conformal-certificate assumption. -/
theorem cauchyInverse_analyticOnNhd {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    AnalyticOnNhd ℂ (cauchyInverse φ) (cauchyImage φ) :=
  (cauchyInverse_differentiableOn hφ hodd hzero hpos).analyticOnNhd
    (cauchyImage_isOpen hφ hodd hzero hpos)

theorem cauchy_conformalAt {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ upperHalfPlane) : ConformalAt (cauchy φ) z :=
  (hasDerivAt_cauchy hφ.continuousOn hz).differentiableAt.conformalAt
    (cauchy_derivative_ne_zero hφ hodd hzero hpos hz)

/-- The actual Cauchy map and its constructed inverse form a homeomorphism
between H and its actual image. This does not assert boundary extension. -/
def cauchyHomeomorph {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    upperHalfPlane ≃ₜ cauchyImage φ where
  toFun z := ⟨cauchy φ z, ⟨z, z.property, rfl⟩⟩
  invFun w := ⟨cauchyInverse φ w, cauchyInverse_mem w.property⟩
  left_inv z := Subtype.ext (cauchyInverse_cauchy hφ hodd hzero hpos z.property)
  right_inv w := Subtype.ext (cauchy_cauchyInverse w.property)
  continuous_toFun := ((cauchy_differentiableOn hφ.continuousOn).continuousOn.restrict).subtype_mk _
  continuous_invFun :=
    ((cauchyInverse_differentiableOn hφ hodd hzero hpos).continuousOn.restrict).subtype_mk _

end Torsion.Spectral

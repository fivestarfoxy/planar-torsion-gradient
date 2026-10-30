module

public import Torsion.ConformalGreenRegularPart
public import Torsion.GreenRegularPart

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual weak Green equation on the Cauchy image

The divided difference of the genuine holomorphic inverse removes the
physical logarithmic pole. Its nonvanishing gives a smooth harmonic regular
part throughout the image, including the pole. The original compact smooth
tests then give the correctly normalized weak source equation.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion.Spectral

/-- The true smooth regular part, including its value at the physical pole. -/
def physicalGreenRegular (φ : ℝ → ℝ) (v : Plane) : Plane → ℝ :=
  HalfPlane.conformalGreenRegular (cauchyInverse φ) v

theorem cauchyInverse_injOn_image (φ : ℝ → ℝ) :
    Set.InjOn (cauchyInverse φ) (cauchyImage φ) := by
  intro w hw v hv h
  rw [← cauchy_cauchyInverse hw, ← cauchy_cauchyInverse hv, h]

theorem cauchyInverse_deriv_ne_zero {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {v : Plane} (hv : v ∈ cauchyImage φ) : deriv (cauchyInverse φ) v ≠ 0 := by
  obtain ⟨z, hz, rfl⟩ := hv
  rw [(cauchyInverse_hasDerivAt hφ hodd hzero hpos hz).deriv]
  exact inv_ne_zero (cauchy_derivative_ne_zero hφ hodd hzero hpos hz)

/-- The actual physical kernel splits into the normalized planar source
and a genuine harmonic regular part, rather than only having an asymptotic
logarithmic coefficient. -/
theorem physicalGreen_eq_fundamental_add_regular {φ : ℝ → ℝ}
    {v w : Plane} (hv : v ∈ cauchyImage φ) (hw : w ∈ cauchyImage φ)
    (hne : w ≠ v) :
    physicalGreen φ w v = HalfPlane.fundamental v w + physicalGreenRegular φ v w := by
  exact HalfPlane.green_comp_eq_fundamental_add_regular hne
    (fun h => hne (cauchyInverse_injOn_image φ hw hv h))

theorem physicalGreenRegular_contDiffOn {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {v : Plane} (hv : v ∈ cauchyImage φ) :
    ContDiffOn ℝ ∞ (physicalGreenRegular φ v) (cauchyImage φ) :=
  HalfPlane.conformalGreenRegular_contDiffOn (cauchyImage_isOpen hφ hodd hzero hpos)
    (cauchyInverse_differentiableOn hφ hodd hzero hpos) (cauchyInverse_injOn_image φ)
    (fun _ hw => cauchyInverse_mem hw) hv (cauchyInverse_deriv_ne_zero hφ hodd hzero hpos hv)

theorem physicalGreenRegular_laplacian_eq_zero {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {v w : Plane} (hv : v ∈ cauchyImage φ) (hw : w ∈ cauchyImage φ) :
    WeakHarmonicRegularity.planarLaplacian (physicalGreenRegular φ v) w = 0 :=
  HalfPlane.conformalGreenRegular_laplacian_eq_zero (cauchyImage_isOpen hφ hodd hzero hpos)
    (cauchyInverse_differentiableOn hφ hodd hzero hpos) (cauchyInverse_injOn_image φ)
    (fun _ hx => cauchyInverse_mem hx) hv (cauchyInverse_deriv_ne_zero hφ hodd hzero hpos hv) hw

/-- The Green gradient pairs integrably with every original compact smooth
test on the actual physical domain. The pole is handled by the actual
fundamental-solution integrability theorem. -/
theorem physicalGreen_pairing_integrable {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {v : Plane} (hv : v ∈ cauchyImage φ) {ψ : Plane → ℝ}
    (hψ : IsTest (cauchyImage φ) ψ) :
    Integrable (fun w => inner (𝕜 := ℝ)
      (gradient (fun u => physicalGreen φ u v) w) (gradient ψ w)) := by
  exact (green_regular_part_weak_source (cauchyImage_isOpen hφ hodd hzero hpos)
    (physicalGreenRegular_contDiffOn hφ hodd hzero hpos hv)
    (fun _ hw => physicalGreenRegular_laplacian_eq_zero hφ hodd hzero hpos hv hw)
    (fun _ hw hne => physicalGreen_eq_fundamental_add_regular hv hw hne) hψ).1

/-- The constructed logarithmic kernel satisfies `-ΔG(·,v)=δ_v` in the
actual physical domain with coefficient exactly one. No Green equation,
conformal weak transport or source normalization is assumed. -/
theorem physicalGreen_weak_source {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {v : Plane} (hv : v ∈ cauchyImage φ) {ψ : Plane → ℝ}
    (hψ : IsTest (cauchyImage φ) ψ) :
    (∫ w in cauchyImage φ, inner (𝕜 := ℝ)
      (gradient (fun u => physicalGreen φ u v) w) (gradient ψ w)) = ψ v := by
  exact (green_regular_part_weak_source (cauchyImage_isOpen hφ hodd hzero hpos)
    (physicalGreenRegular_contDiffOn hφ hodd hzero hpos hv)
    (fun _ hw => physicalGreenRegular_laplacian_eq_zero hφ hodd hzero hpos hv hw)
    (fun _ hw hne => physicalGreen_eq_fundamental_add_regular hv hw hne) hψ).2

end Torsion.Spectral

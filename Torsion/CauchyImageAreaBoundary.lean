module

public import Torsion.CauchyImageArea
public import Torsion.CauchyConformalGeometry.BoundaryDerivative
public import Torsion.CauchySpectralIdentity
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Rectangle area identities for the actual Cauchy map

The continuous field `Im(F) F′` on the closed half-plane has real curl
`-‖F′‖²` in the open half-plane. The rectangle form of Green's theorem
therefore relates the genuine Jacobian energy to the actual boundary
values. No signed-area formula is postulated.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal Interval

namespace Torsion.Spectral

/-- The continuous boundary field used to calculate Cauchy image area. -/
def cauchyAreaField (φ : ℝ → ℝ) (z : Plane) : Plane :=
  ((cauchyExtension φ z).im : ℂ) * cauchyDerivativeExtension φ z

/-- A real derivative field for `Im(F) F′` in the open half-plane.
The formula is also defined on the axis; no derivative there is asserted. -/
def cauchyAreaFieldDerivative (φ : ℝ → ℝ) (z : Plane) : Plane →L[ℝ] Plane :=
  ((cauchyExtension φ z).im : ℂ) •
    (deriv (deriv (cauchy φ)) z • (1 : Plane →L[ℝ] Plane)) +
  (cauchyDerivativeExtension φ z) •
    (Complex.ofRealCLM.comp (Complex.imCLM.comp
      (cauchyDerivativeExtension φ z • (1 : Plane →L[ℝ] Plane))))

/-- Cancellation in the area derivative field is pointwise algebra and
remains valid at the axis, independent of any second boundary derivative. -/
theorem cauchyAreaFieldDerivative_curl (φ : ℝ → ℝ) (z : Plane) :
    Complex.I * cauchyAreaFieldDerivative φ z 1 -
      cauchyAreaFieldDerivative φ z Complex.I =
        -((‖cauchyDerivativeExtension φ z‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [cauchyAreaFieldDerivative, ContinuousLinearMap.comp_apply, Complex.mul_re,
      Complex.mul_im, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] <;> ring

/-- The derivative field is the actual Fréchet derivative at every interior
point, proved from holomorphy and the actual Cauchy extensions. -/
theorem cauchyAreaField_hasFDerivAt {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    HasFDerivAt (cauchyAreaField φ) (cauchyAreaFieldDerivative φ z) z := by
  have hF := (hasDerivAt_cauchy hφ.continuousOn hz).differentiableAt.hasDerivAt.complexToReal_fderiv
  have hD := ((cauchy_analyticOnNhd hφ.continuousOn).deriv z hz).differentiableAt.hasDerivAt.complexToReal_fderiv
  have hY := Complex.ofRealCLM.hasFDerivAt.comp z (Complex.imCLM.hasFDerivAt.comp z hF)
  have h := hY.mul hD
  have hcorrect : HasFDerivAt
      (fun w => ((cauchy φ w).im : ℂ) * deriv (cauchy φ) w)
      (cauchyAreaFieldDerivative φ z) z := by
    simpa only [cauchyAreaFieldDerivative, cauchyExtension_eq hφ.continuousOn hz,
      cauchyDerivativeExtension_eq hφ hodd hzero hz, Function.comp_def,
      Complex.ofRealCLM_apply, Complex.imCLM_apply, Pi.mul_def] using! h
  apply hcorrect.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
  simp only [cauchyAreaField, cauchyExtension_eq hφ.continuousOn hw,
    cauchyDerivativeExtension_eq hφ hodd hzero hw]

/-- Continuity up to the entire real axis comes from the actual continuous
extensions, rather than from an assumed boundary field. -/
theorem cauchyAreaField_continuousOn {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    ContinuousOn (cauchyAreaField φ) (closure upperHalfPlane) := by
  obtain ⟨hF, hD, _, _⟩ := cauchy_extensions_diffContOnCl_of_holder
    hφ hα0 hα1 hodd hzero
  exact (Complex.continuous_ofReal.comp_continuousOn
    (Complex.continuous_im.comp_continuousOn hF.continuousOn)).mul hD.continuousOn

/-- The real component of the actual boundary field is supported on the
closed free interval and has its exact linear-equation value there. -/
theorem cauchyAreaField_ofReal_re {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) (x : ℝ) :
    (cauchyAreaField φ (x : Plane)).re = height φ x * (b - a * height φ x) := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have hv := cauchyDerivativeExtension_re_eq_boundaryVelocity hφ hα0 hzero hlinear x hx
    simp only [cauchyAreaField, cauchyExtension_ofReal, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      zero_mul, add_zero, zero_add, Complex.mul_re, sub_zero, hv, boundaryVelocity]
  · have hy : height φ x = 0 := height_zero_of_one_le_abs φ (by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hl | hr
      · have h := neg_le_abs x
        linarith
      · exact (le_of_lt hr).trans (le_abs_self x))
    simp [cauchyAreaField, cauchyExtension_ofReal, hy]

/-- Green's rectangle theorem for the actual continuous boundary field.
The entire bottom side lies on the real axis; differentiability is used
only in the open upper half-plane. -/
theorem cauchyAreaField_rectangle_identity {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : ℝ in -R..R, cauchyAreaField φ (x : Plane)) -
      (∫ x : ℝ in -R..R, cauchyAreaField φ ((x : Plane) + (R : Plane) * Complex.I)) +
      Complex.I * (∫ y : ℝ in (0 : ℝ)..R,
        cauchyAreaField φ ((R : Plane) + (y : Plane) * Complex.I)) -
      Complex.I * (∫ y : ℝ in (0 : ℝ)..R,
        cauchyAreaField φ ((-R : Plane) + (y : Plane) * Complex.I)) =
      -((∫ x : ℝ in -R..R, ∫ y : ℝ in (0 : ℝ)..R,
        ‖cauchyDerivativeExtension φ ((x : Plane) + (y : Plane) * Complex.I)‖ ^ 2 : ℝ) : ℂ) := by
  let K : Set Plane := Icc (-R) R ×ℂ Icc 0 R
  have hRK : -R ≤ R := by linarith
  have hK : K ⊆ closure upperHalfPlane := by
    intro z hz
    rw [upperHalfPlane, Complex.closure_setOf_lt_im]
    exact hz.2.1
  have hcompact : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hD := (cauchyDerivativeExtension_diffContOnCl hφ hα0 hzero).continuousOn.mono hK
  have hc := (cauchyAreaField_continuousOn hφ hα0 hα1 hodd hzero).mono hK
  have hi : IntegrableOn (fun z => -((‖cauchyDerivativeExtension φ z‖ ^ 2 : ℝ) : ℂ)) K :=
    ((Complex.continuous_ofReal.comp_continuousOn (hD.norm.pow 2)).neg).integrableOn_compact hcompact
  have heq := Complex.integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real
    (cauchyAreaField φ) (cauchyAreaFieldDerivative φ) ⟨-R, 0⟩ ⟨R, R⟩
    (by simpa only [uIcc_of_le hRK, uIcc_of_le hR] using hc)
    (by
      intro z hz
      have hy : z ∈ upperHalfPlane := by
        simpa only [upperHalfPlane, mem_setOf_eq] using
          (show z.im ∈ Ioo (0 : ℝ) R from by
            simpa only [Set.mem_preimage, min_eq_left hR,
              max_eq_right hR] using hz.2).1
      exact cauchyAreaField_hasFDerivAt (hφ.continuous hα0) hodd hzero hy)
    (by
      simpa only [uIcc_of_le hRK, uIcc_of_le hR,
        smul_eq_mul, cauchyAreaFieldDerivative_curl] using hi)
  simpa only [Complex.ofReal_zero, zero_mul, add_zero,
    smul_eq_mul, cauchyAreaFieldDerivative_curl, intervalIntegral.integral_neg,
    intervalIntegral.integral_ofReal, Complex.ofReal_neg] using heq

end Torsion.Spectral

module

public import Torsion.RestrictedSpectralForm.Algebra
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smooth-test admission for the restricted spectral weak equation

Every smooth compact test in the interval is proved to have finite actual
half-derivative energy, by Fourier–Schwartz decay. Thus the restricted weak
equation genuinely applies to arbitrary ordinary compact smooth tests.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- The first weighted squared Fourier moment of a Schwartz function is
integrable. Boundedness supplies one factor; Schwartz decay supplies the other. -/
theorem SchwartzMap_integrable_abs_mul_norm_sq (S : 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ : ℝ => |ξ| * ‖S ξ‖ ^ 2) := by
  let C := SchwartzMap.seminorm ℝ 0 0 S
  have hi : Integrable (fun ξ : ℝ => ‖ξ‖ * ‖S ξ‖) := by
    simpa only [pow_one] using S.integrable_pow_mul volume 1
  apply (hi.const_mul C).mono'
    ((continuous_abs.mul (S.continuous.norm.pow 2)).aestronglyMeasurable)
  exact ae_of_all _ fun ξ => by
    change ‖|ξ| * ‖S ξ‖ ^ 2‖ ≤ C * (‖ξ‖ * ‖S ξ‖)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    calc
      |ξ| * ‖S ξ‖ ^ 2 = (|ξ| * ‖S ξ‖) * ‖S ξ‖ := by ring
      _ ≤ (|ξ| * ‖S ξ‖) * C :=
        mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ S ξ)
          (mul_nonneg (abs_nonneg ξ) (norm_nonneg _))
      _ = C * (‖ξ‖ * ‖S ξ‖) := by rw [Real.norm_eq_abs]; ring

/-- Genuine finite Fourier half energy of a compact smooth function. -/
theorem finiteEnergy_of_contDiff_hasCompactSupport {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) : FiniteEnergy ψ := by
  let ψS := compactSmoothSchwartz hψ hc
  let S := SchwartzMap.fourierTransformCLM ℂ ψS
  have hF (ξ : ℝ) : fourier ψ ξ = S (ξ / (2 * Real.pi)) :=
    fourier_eq_mathlib ψ ξ
  have hp : 0 < 2 * Real.pi := by positivity
  have hi := (SchwartzMap_integrable_abs_mul_norm_sq S).comp_div hp.ne'
  unfold FiniteEnergy
  convert hi.const_mul (2 * Real.pi) using 1
  funext ξ
  rw [hF, abs_div, abs_of_pos hp]
  field_simp

/-- Every ordinary restricted smooth test is admitted by the actual closed
form domain, using the constant approximating sequence. -/
theorem IsCore.memRestrictedFormDomain {ψ : ℝ → ℝ} (hψ : IsCore ψ) :
    MemRestrictedFormDomain ψ := by
  refine ⟨hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1,
    finiteEnergy_of_contDiff_hasCompactSupport hψ.1 hψ.2.1, ?_,
    (fun _ => ψ), (fun _ => hψ), ?_, ?_⟩
  · exact ae_of_all _ fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hψ.2.2 h))
  · simp
  · simp [energy, fourier]

/-- The nonzero restricted eigenfunction satisfies its Fourier weak equation
against every classical compact smooth test in the interval. -/
theorem IsRestrictedEigenfunction.core_equation {a : ℝ} {φ : ℝ → ℝ}
    (hφ : IsRestrictedEigenfunction a φ) {ψ : ℝ → ℝ} (hψ : IsCore ψ) :
    (1 / (2 * Real.pi)) *
      (∫ ξ : ℝ, |ξ| * (fourier φ ξ * star (fourier ψ ξ)).re) =
        a * ∫ x : ℝ, φ x * ψ x :=
  hφ.2.2 ψ hψ.memRestrictedFormDomain

end Torsion.Spectral

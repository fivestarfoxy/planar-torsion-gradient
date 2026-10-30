import Torsion.PhysicalCauchyHarmonicBoundary
import Torsion.CauchyTransformIntegrationByParts
import Torsion.CauchyTransformMoments
import Torsion.CauchyTransformImageBound
import Torsion.RadialDeformationCollar

/-!
# Actual derivatives of smooth compact-data harmonic lifts

Integration by parts identifies the derivative with the Cauchy transform
of the actual derivative of the boundary data. Smooth compact data supply
the required global Hölder estimate without a regularity certificate.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral

theorem realCauchy_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    HasDerivAt (realCauchy g) ((Real.pi : Plane)⁻¹ *
      ∫ s in Icc (-1 : ℝ) 1, (g s : Plane) / (z - (s : Plane)) ^ 2) z := by
  simpa only [realCauchy, neg_div, integral_neg, neg_mul_neg] using
    (hasDerivAt_cauchy_integral (Complex.continuous_ofReal.comp hg).continuousOn hz).const_mul
      (-((Real.pi : Plane)⁻¹))

theorem deriv_realCauchy_eq_realCauchy_deriv {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hm : g (-1) = 0) (hp : g 1 = 0)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    deriv (realCauchy g) z = realCauchy (deriv g) z := by
  rw [(realCauchy_hasDerivAt hg.continuous hz).deriv,
    cauchy_integrationByParts_of_hasDerivAt hg.continuous (hg.continuous_deriv (by simp))
      (fun x => ((hg.differentiable (by simp)) x).hasDerivAt) hm hp hz]
  simp only [realCauchy, mul_neg, neg_mul]

theorem smooth_compact_deriv_holder {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ K : ℝ≥0, HolderWith K 1 (deriv g) := by
  have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  obtain ⟨K, hK⟩ := Shape.exists_lipschitz_scalar_of_contDiff_compact hgd hgc.deriv
  exact ⟨K, hK.holderWith⟩

theorem smooth_compact_interval_zero {g : ℝ → ℝ}
    (hgs : tsupport g ⊆ Ioo (-1 : ℝ) 1) :
    (∀ x : ℝ, 1 ≤ |x| → g x = 0) ∧ (∀ x : ℝ, 1 ≤ |x| → deriv g x = 0) := by
  constructor
  · intro x hx
    by_contra hn
    have h := hgs (subset_tsupport g hn)
    have ha : |x| < 1 := abs_lt.mpr h
    linarith
  · intro x hx
    by_contra hn
    have h := hgs (support_deriv_subset hn)
    have ha : |x| < 1 := abs_lt.mpr h
    linarith

/-- Smooth compact boundary data supply a genuine continuous extension of
their actual holomorphic derivative to the entire closed half-plane. -/
theorem realCauchy_derivative_extension_of_compactSmooth {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ Ioo (-1 : ℝ) 1) :
    ContinuousOn (realCauchyExtension (deriv g)) (closure upperHalfPlane) ∧
      ∀ z ∈ upperHalfPlane, realCauchyExtension (deriv g) z = deriv (realCauchy g) z := by
  obtain ⟨K, hK⟩ := smooth_compact_deriv_holder hg hgc
  have hzero := smooth_compact_interval_zero hgs
  refine ⟨realCauchyExtension_continuousOn hK (by norm_num) hzero.2, ?_⟩
  intro z hz
  rw [realCauchyExtension_eq (hg.continuous_deriv (by simp)) hzero.2 hz,
    deriv_realCauchy_eq_realCauchy_deriv hg (hzero.1 (-1) (by norm_num))
      (hzero.1 1 (by norm_num)) hz]

theorem physicalHarmonicLift_hasGradientAt_cauchy {φ g : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) (hg : Continuous g)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    HasGradientAt (physicalHarmonicLift φ g)
      (Complex.I * star (deriv (realCauchy g) z / deriv (cauchy φ) z)) (cauchy φ z) := by
  have hG := (realCauchy_differentiableOn hg).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
  have hInv := cauchyInverse_hasDerivAt hφ hodd hzero hpos hz
  have h := hG.hasDerivAt.comp_of_eq _ hInv (cauchyInverse_cauchy hφ hodd hzero hpos hz).symm
  simpa only [physicalHarmonicLift, Function.comp_def, div_eq_mul_inv] using
    PhysicalTorsion.hasGradientAt_im_of_hasDerivAt h

theorem realCauchy_derivative_moment {g : ℝ → ℝ}
    (hg : Continuous g) {A : Type*} {l : Filter A} {z : A → Plane}
    (hz : Tendsto (fun a => ‖z a‖) l atTop) (hH : ∀ᶠ a in l, z a ∈ upperHalfPlane) :
    Tendsto (fun a => z a ^ 2 * deriv (realCauchy g) (z a)) l
      (𝓝 ((Real.pi : Plane)⁻¹ * ((∫ s in Icc (-1 : ℝ) 1, g s : ℝ) : Plane))) := by
  have h := (cauchy_square_integral_moment
    (Complex.continuous_ofReal.comp hg).continuousOn hz).const_mul ((Real.pi : Plane)⁻¹)
  simp only [Function.comp_apply, integral_complex_ofReal] at h
  apply h.congr'
  filter_upwards [hH] with a ha
  rw [(realCauchy_hasDerivAt hg ha).deriv]
  ring

end Torsion.Spectral

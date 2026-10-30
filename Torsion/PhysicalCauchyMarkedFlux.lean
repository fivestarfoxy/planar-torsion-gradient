import Torsion.CauchyConformalGeometry.MarkedGeometry
import Torsion.PhysicalCauchyWeakTorsion
import Torsion.PhysicalCauchyBoundary
import Torsion.MarkedFluxLowerBound

/-!
# The actual marked torsion flux of the Cauchy image

The image is proved marked, and the physical formula is proved weak torsion.
The constructed smooth marked representative can therefore be compared with
the physical gradient along `F(i(n+1))`. Its continuity at the marked point
and the actual infinity limit identify the original PDE flux as `b/a`.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace Torsion.Spectral

/-- The flux in equation (18) belongs to the actual weak torsion solution on
the actual marked Cauchy image. No marked-flux identity is assumed. -/
theorem physicalCandidate_hasTorsionFlux {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    HasTorsionFlux (cauchyImage φ) (b / a) := by
  have hc := hφ.continuous hα0
  have hmarked := cauchyImage_isMarked hφ hα0 hα1 hodd hzero hpos
  have hweak := physicalCandidate_isWeakTorsion ha hφ hα0 hα1 hodd hzero hpos hlinear
  obtain ⟨r, v, hr, hv, hsub, hv0, hvalue, hgrad⟩ :=
    hmarked.exists_smooth_torsion_representative hweak
  let U : Set Plane := upperHalfPlane ∩ Metric.ball 0 r
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball
  have hgv : Continuous (gradient v) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp
      (hv.continuous_fderiv (by simp))
  have hgrad' : gradient (physicalCandidate φ) =ᵐ[volume.restrict U] gradient v := by
    filter_upwards [hgrad, ae_restrict_mem hU.measurableSet] with w hw hwU
    rw [← physicalZeroGradient_eq (hsub hwU)]
    exact hw
  have hpoint : EqOn (gradient (physicalCandidate φ)) (gradient v) U :=
    Measure.eqOn_open_of_ae_eq hgrad' hU
      ((physicalCandidate_gradient_continuousOn hc hodd hzero hpos).mono hsub)
      hgv.continuousOn
  let z : ℕ → Plane := fun n => (((n : ℝ) + 1 : ℝ) : Plane) * Complex.I
  have hzH (n : ℕ) : z n ∈ upperHalfPlane := by
    simp only [z, upperHalfPlane, mem_setOf_eq, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero]
    positivity
  have hznorm : Tendsto (fun n => ‖z n‖) atTop atTop := by
    have heq : (fun n => ‖z n‖) = fun n : ℕ => (n : ℝ) + 1 := by
      funext n
      simp only [z, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    rw [heq]
    exact tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hF0 := cauchy_tendsto_zero hc.continuousOn hznorm
  have hFU : ∀ᶠ n in atTop, cauchy φ (z n) ∈ U := by
    have hsmall := hF0.eventually (Metric.ball_mem_nhds (0 : Plane) hr)
    filter_upwards [hsmall] with n hn
    exact ⟨cauchy_im_pos hc.continuousOn hpos (hzH n), hn⟩
  have hphysical := gradient_physicalCandidate_cauchy_tendsto_at_infinity
    ha hφ hα0 hα1 hodd hzero hpos hlinear hznorm (Eventually.of_forall hzH)
  have hvlimit : Tendsto (fun n => gradient v (cauchy φ (z n))) atTop (𝓝 (gradient v 0)) :=
    hgv.continuousAt.tendsto.comp hF0
  have hsame : (fun n => gradient v (cauchy φ (z n))) =ᶠ[atTop]
      (fun n => gradient (physicalCandidate φ) (cauchy φ (z n))) := by
    filter_upwards [hFU] with n hn
    exact (hpoint hn).symm
  have hvg : gradient v 0 = ((b / a : ℝ) : ℂ) * Complex.I :=
    tendsto_nhds_unique hvlimit (hphysical.congr' hsame.symm)
  have hflux := HasTorsionFlux.of_localRepresentative hweak hr hv.continuous.continuousOn
    hvalue hv0 (hv.differentiable (by simp) 0)
  simpa only [hvg, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero] using hflux

/-- The already constructed, representative-independent PDE flux of the
actual Cauchy image is exactly the spectral coefficient ratio. -/
theorem torsionFlux_cauchyImage {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    torsionFlux (cauchyImage φ) = b / a :=
  ((physicalCandidate_hasTorsionFlux ha hφ hα0 hα1 hodd hzero hpos hlinear).eq_torsionFlux
    (cauchyImage_isMarked hφ hα0 hα1 hodd hzero hpos)).symm

/-- The same genuine PDE flux is the ratio of the two concrete height
moments in equation (18). -/
theorem torsionFlux_cauchyImage_eq_squareMass_div_mass
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    torsionFlux (cauchyImage φ) = squareMass φ / (2 * mass φ) := by
  rw [torsionFlux_cauchyImage ha hφ hα0 hα1 hodd hzero hpos hlinear]
  have hM := (mass_pos (hφ.continuous hα0).continuousOn hpos).ne'
  have hmoment := moment_identity_of_holder_boundary_equation
    ha hφ hα0 hα1 hodd hzero hlinear
  apply (div_eq_div_iff ha (mul_ne_zero (by norm_num) hM)).2
  nlinarith [hmoment]

/-- The exact marked flux yields a lower bound on the actual interior
essential gradient norm of the proved weak torsion solution. -/
theorem physicalCandidate_markedFlux_le_eLpNorm
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    ENNReal.ofReal (b / a) ≤
      eLpNorm (physicalZeroGradient φ) ∞ (volume.restrict (cauchyImage φ)) := by
  rw [← torsionFlux_cauchyImage ha hφ hα0 hα1 hodd hzero hpos hlinear]
  exact torsionFlux_le_eLpNorm (cauchyImage_isMarked hφ hα0 hα1 hodd hzero hpos)
    (physicalCandidate_isWeakTorsion ha hφ hα0 hα1 hodd hzero hpos hlinear)

end Torsion.Spectral

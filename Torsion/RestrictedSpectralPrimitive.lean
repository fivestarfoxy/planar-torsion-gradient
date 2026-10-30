module

public import Torsion.RestrictedSpectralDistribution
public import Torsion.CauchyTransformImaginaryBoundary
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fourier differentiation and the integrated weak spectral equation

The actual integrated odd profile satisfies the differentiated weak
half-Laplacian equation.  This is proved from the Fourier-form eigenfunction
equation, not from an assumed Hilbert boundary equation.  Identifying this
Fourier distribution with the continuous Hilbert trace is a separate step.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- Continuity upgrades the actual form-domain zero-exterior condition
from an a.e. statement to all exterior points, including the two endpoints. -/
theorem MemRestrictedFormDomain.zero_exterior {φ : ℝ → ℝ}
    (hmem : MemRestrictedFormDomain φ) (hφ : Continuous φ) :
    ∀ x : ℝ, 1 ≤ |x| → φ x = 0 := by
  have hpos : EqOn φ (fun _ => 0) (Ioi (1 : ℝ)) := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) _ isOpen_Ioi hφ.continuousOn continuousOn_const
    apply (ae_restrict_iff' measurableSet_Ioi).2
    filter_upwards [hmem.2.2.1] with x hx hxi
    exact hx (by intro h; exact (not_lt_of_ge (le_of_lt hxi)) h.2)
  have hneg : EqOn φ (fun _ => 0) (Iio (-1 : ℝ)) := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) _ isOpen_Iio hφ.continuousOn continuousOn_const
    apply (ae_restrict_iff' measurableSet_Iio).2
    filter_upwards [hmem.2.2.1] with x hx hxi
    exact hx (by intro h; exact (not_lt_of_ge (le_of_lt h.1)) hxi)
  have hpos' : EqOn φ (fun _ => 0) (Ici (1 : ℝ)) :=
    hpos.of_subset_closure hφ.continuousOn continuousOn_const (Ioi_subset_Ici le_rfl)
      (by rw [closure_Ioi])
  have hneg' : EqOn φ (fun _ => 0) (Iic (-1 : ℝ)) :=
    hneg.of_subset_closure hφ.continuousOn continuousOn_const (Iio_subset_Iic le_rfl)
      (by rw [closure_Iio])
  intro x hx
  rcases le_or_gt 0 x with hp | hn
  · apply hpos'
    simpa only [mem_Ici, abs_of_nonneg hp] using hx
  · apply hneg'
    have hx' : 1 ≤ -x := by simpa only [abs_of_neg hn] using hx
    change x ≤ -1
    linarith

/-- Differentiation in the source's `exp(-ixξ)` Fourier convention. -/
theorem fourier_deriv {f : ℝ → ℝ} (hf : Integrable f)
    (hd : Differentiable ℝ f) (hdf : Integrable (deriv f)) (ξ : ℝ) :
    fourier (deriv f) ξ = (ξ : ℂ) * Complex.I * fourier f ξ := by
  let fc : ℝ → ℂ := fun x => (f x : ℂ)
  have hdc (x : ℝ) : deriv fc x = ((deriv f x : ℝ) : ℂ) :=
    ((hd x).hasDerivAt.ofReal_comp).deriv
  have hdeq : deriv fc = fun x => ((deriv f x : ℝ) : ℂ) := funext hdc
  have hc : Integrable fc := Complex.ofRealCLM.integrable_comp hf
  have hcd : Differentiable ℝ fc := fun x =>
    ((hd x).hasDerivAt.ofReal_comp).differentiableAt
  have hcdint : Integrable (deriv fc) := by
    rw [hdeq]
    exact Complex.ofRealCLM.integrable_comp hdf
  have h := congrFun (Real.fourier_deriv hc hcd hcdint)
    (ξ / (2 * Real.pi))
  rw [fourier_eq_mathlib, fourier_eq_mathlib]
  simp only [hdeq, smul_eq_mul] at h
  rw [h]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfac : (2 : ℂ) * (Real.pi : ℂ) * Complex.I *
      ((ξ / (2 * Real.pi) : ℝ) : ℂ) = (ξ : ℂ) * Complex.I := by
    push_cast
    field_simp [hpi]
  rw [hfac]

/-- The concrete height's Fourier transform is an antiderivative of the
actual zero-extended odd eigenfunction. -/
theorem fourier_height_identity {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (ξ : ℝ) :
    fourier φ ξ = -(ξ : ℂ) * Complex.I * fourier (height φ) ξ := by
  have hY : Integrable (height φ) := height_integrable hφ.continuousOn
  have hφint : Integrable φ := hφ.integrable_of_hasCompactSupport
    (cauchyDensity_hasCompactSupport hzero)
  have hYd : Differentiable ℝ (height φ) :=
    fun x => (hasDerivAt_height hφ hodd hzero x).differentiableAt
  have hderiv : deriv (height φ) = fun x => -φ x :=
    funext (deriv_height_eq hφ hodd hzero)
  have hint : Integrable (deriv (height φ)) := by
    rw [hderiv]
    exact hφint.neg
  have h := fourier_deriv hY hYd hint ξ
  rw [hderiv] at h
  have hneg : fourier (fun x => -φ x) ξ = -fourier φ ξ := by
    have heq : (fun x => -φ x) = fun x => (-1 : ℝ) * φ x := by funext x; ring
    rw [heq, fourier_const_mul]
    simp
  rw [hneg] at h
  linear_combination -h

/-- Integrating an actual finite-energy odd profile preserves finite
half-Laplacian energy. Near frequency zero use continuity, and away from zero
use the proved Fourier primitive identity and the original finite energy. -/
theorem finiteEnergy_height {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (he : FiniteEnergy φ) :
    FiniteEnergy (height φ) := by
  let g : ℝ → ℝ := fun ξ => |ξ| * ‖fourier (height φ) ξ‖ ^ 2
  have hg : Continuous g := continuous_abs.mul
    ((fourier_continuous (height_integrable hφ.continuousOn)).norm.pow 2)
  have hnear : IntegrableOn g (Icc (-1 : ℝ) 1) := hg.integrableOn_Icc
  have hfar : IntegrableOn g (Icc (-1 : ℝ) 1)ᶜ := by
    apply he.integrableOn.mono' hg.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with ξ hξ
    have hξabs : 1 ≤ |ξ| := by
      by_contra h
      have hlt : |ξ| < 1 := lt_of_not_ge h
      exact hξ (abs_le.mp hlt.le)
    have hnorm : ‖fourier φ ξ‖ = |ξ| * ‖fourier (height φ) ξ‖ := by
      rw [fourier_height_identity hφ hodd hzero]
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hle : ‖fourier (height φ) ξ‖ ≤ ‖fourier φ ξ‖ := by
      rw [hnorm]
      exact le_mul_of_one_le_left (norm_nonneg _) hξabs
    change ‖|ξ| * ‖fourier (height φ) ξ‖ ^ 2‖ ≤ |ξ| * ‖fourier φ ξ‖ ^ 2
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hle 2)
      (abs_nonneg _)
  have hall := hnear.union hfar
  simpa only [union_compl_self, integrableOn_univ, FiniteEnergy, g] using hall

/-- Commutation of the concrete Fourier half-Laplacian form with taking
the odd primitive.  The smooth test's derivative is taken on the other side
of the bilinear pairing, so the signs cancel exactly. -/
theorem energy_height_deriv {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    energy (height φ) (deriv ψ) = energy φ ψ := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hdi : Integrable (deriv ψ) :=
    hdc.integrable_of_hasCompactSupport hc.deriv
  unfold energy
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    dsimp only
    rw [fourier_deriv (hψ.continuous.integrable_of_hasCompactSupport hc) hd hdi,
      fourier_height_identity hφ hodd hzero]
    congr 2
    simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I,
      neg_mul, mul_neg]
    ring

/-- Integration by parts for the actual height and an arbitrary compact
smooth test. -/
theorem integral_height_mul_deriv {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ x : ℝ, height φ x * deriv ψ x) = ∫ x : ℝ, φ x * ψ x := by
  have hY : Continuous (height φ) := height_continuous hφ.continuousOn
  have hd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hasDerivAt_height hφ hodd hzero x) (fun x _ => (hd x).hasDerivAt)
    ((hY.mul hdc).integrable_of_hasCompactSupport (hc.deriv.mul_left))
    (((hφ.neg).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left)
    ((hY.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left)
  simpa only [Pi.mul_apply, Pi.neg_apply, neg_mul, integral_neg, neg_neg] using h

/-- Direct spectral consequence: the distributional derivative of
`L(height φ) - a * height φ` vanishes on the interval.  This theorem uses
`IsRestrictedEigenfunction`, and does not assume the linear Hilbert equation. -/
theorem IsRestrictedEigenfunction.height_derivative_equation
    {a : ℝ} {φ : ℝ → ℝ} (hEig : IsRestrictedEigenfunction a φ)
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    {ψ : ℝ → ℝ} (hψ : IsCore ψ) :
    energy (height φ) (deriv ψ) =
      a * ∫ x : ℝ, height φ x * deriv ψ x := by
  have hzero := hEig.1.zero_exterior hφ
  rw [energy_height_deriv hφ hodd hzero hψ.1 hψ.2.1,
    integral_height_mul_deriv hφ hodd hzero hψ.1 hψ.2.1]
  exact hEig.2.2 ψ hψ.memRestrictedFormDomain

end Torsion.Spectral

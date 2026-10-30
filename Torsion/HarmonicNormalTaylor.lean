module

public import Torsion.ConvolutionDerivativeBounds
public import Torsion.RealTaylorBound
public import Torsion.LocalHarmonicBound
public import Torsion.MarkedBoundaryRegularity

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Fixed-ball normal Taylor estimates for actual weak harmonic functions

The actual smooth Weyl representative has a normal-line remainder bounded
by a fixed directional kernel norm and the weak gradient's local L² norm.
The bound is uniform over all weak functions on the same ball.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Torsion
open WeakHarmonicRegularity

/-- The ordinary normal derivative of a smooth real planar function. -/
theorem normalLine_deriv {v : Plane → ℝ} (hv : ContDiff ℝ ∞ v) (t : ℝ) :
    deriv (fun s : ℝ => v ((s : Plane) * Complex.I)) t =
      (gradient v ((t : Plane) * Complex.I)).im := by
  have hline : HasDerivAt (fun s : ℝ => (s : Plane) * Complex.I) Complex.I t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
  have hd := ((hv.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t hline
  convert hd.deriv using 1
  simp [fderiv_apply_eq_inner_gradient, Complex.inner, Complex.mul_re]

/-- The second normal derivative is the imaginary component of the actual
classical gradient's directional derivative. -/
theorem normalLine_second_deriv {v : Plane → ℝ} (hv : ContDiff ℝ ∞ v) (t : ℝ) :
    deriv (deriv (fun s : ℝ => v ((s : Plane) * Complex.I))) t =
      (fderiv ℝ (gradient v) ((t : Plane) * Complex.I) Complex.I).im := by
  have heq : deriv (fun s : ℝ => v ((s : Plane) * Complex.I)) =
      fun s : ℝ => (gradient v ((s : Plane) * Complex.I)).im := funext (normalLine_deriv hv)
  rw [heq]
  have hline : HasDerivAt (fun s : ℝ => (s : Plane) * Complex.I) Complex.I t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
  have hd := (((gradient_contDiff hv).differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t hline
  exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd).deriv

/-- The fixed, finite nonnegative coefficient in the local normal quotient
estimate. It contains only a directional kernel norm and the actual local
weak-gradient norm. -/
def harmonicNormalTaylorCoefficient (r : ℝ) (g : Plane → Plane) : ℝ :=
  (eLpNorm (fun z => fderiv ℝ (radialKernel r) z Complex.I) 2 volume).toReal *
    (eLpNorm ((Metric.ball (0 : Plane) (2 * r)).indicator g) 2 volume).toReal

theorem harmonicNormalTaylorCoefficient_nonneg (r : ℝ) (g : Plane → Plane) :
    0 ≤ harmonicNormalTaylorCoefficient r g := by
  exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- Constructed actual smooth representatives satisfy one explicit normal
quotient estimate on the full fixed smaller ball. No familywise or boundary
regularity estimate is an additional input. -/
theorem IsWeakHarmonicOn.exists_smoothRepresentative_normal_quotient_bound
    {E : Set Plane} {w : Plane → ℝ} {g : Plane → Plane} {r : ℝ}
    (hw : IsWeakHarmonicOn (Metric.ball 0 (4 * r)) w g)
    (hm : MemH10 E w g) (hr : 0 < r) :
    ∃ v : Plane → ℝ, ContDiff ℝ ∞ v ∧
      (w =ᵐ[volume.restrict (Metric.ball 0 (r / 2))] v) ∧
      (g =ᵐ[volume.restrict (Metric.ball 0 (r / 2))] gradient v) ∧
      ∀ h : ℝ, 0 < h → h < r / 2 →
        |(v ((h : Plane) * Complex.I) - v 0) / h - (gradient v 0).im| ≤
          harmonicNormalTaylorCoefficient r g * h := by
  obtain ⟨v, hv, hAE, hG⟩ := hw.exists_smoothRepresentative_on_ball hm hr Subset.rfl
  have hker := gradient_ae_eq_radial_mollifyGradient_on_ball hm.1 hm.2.1 hw hr Subset.rfl
  have hGsmall : gradient v =ᵐ[volume.restrict (Metric.ball 0 (r / 2))]
      mollifyGradient g (radialKernel r) := hG.symm.trans
    (ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball (half_le_self hr.le)) hker)
  have hpoint := Measure.eqOn_open_of_ae_eq hGsmall Metric.isOpen_ball
    (gradient_contDiff hv).continuous.continuousOn
    (mollifyGradient_contDiff hm.2.1 (radialKernel_contDiff r)
      (radialKernel_hasCompactSupport hr)).continuous.continuousOn
  refine ⟨v, hv, hAE, hG, ?_⟩
  intro h hh hhR
  let f : ℝ → ℝ := fun t => v ((t : Plane) * Complex.I)
  have hf : ContDiff ℝ ∞ f := hv.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hbound : ∀ t ∈ Icc 0 h, |deriv (deriv f) t| ≤ harmonicNormalTaylorCoefficient r g := by
    intro t ht
    have htB : (t : Plane) * Complex.I ∈ Metric.ball (0 : Plane) (r / 2) := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2.trans_lt hhR
    have heq : gradient v =ᶠ[𝓝 ((t : Plane) * Complex.I)]
        mollifyGradient g (radialKernel r) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds htB] with z hz
      exact hpoint hz
    have hnorm := norm_fderiv_mollifyGradient_apply_le_localL2 hm.2.1 hr
      (Metric.ball_subset_ball (half_le_self hr.le) htB) Complex.I
    rw [← heq.fderiv_eq] at hnorm
    change |deriv (deriv (fun s : ℝ => v ((s : Plane) * Complex.I))) t| ≤ _
    rw [normalLine_second_deriv hv]
    exact (Complex.abs_im_le_norm _).trans hnorm
  have htaylor := abs_quotient_sub_deriv_le_of_contDiff_second_deriv_bound hf
    (harmonicNormalTaylorCoefficient_nonneg r g) hh hbound
  simpa only [f, normalLine_deriv hv, Complex.ofReal_zero, zero_mul] using htaylor

/-- A fixed ball has one Taylor coefficient for every locally bounded weak
harmonic function, independent of the global Sobolev extension. -/
theorem exists_uniform_harmonic_normal_quotient_constant {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {E : Set Plane} {w : Plane → ℝ} {g : Plane → Plane} {M : ℝ},
      MemH10 E w g → IsWeakHarmonicOn (Metric.ball 0 (4*r)) w g → 0 ≤ M →
      (∀ᵐ z ∂volume.restrict (Metric.ball (0 : Plane) (4*r)), |w z| ≤ M) →
      ∃ v : Plane → ℝ, ContDiff ℝ ∞ v ∧
        (w =ᵐ[volume.restrict (Metric.ball 0 (r/2))] v) ∧
        (g =ᵐ[volume.restrict (Metric.ball 0 (r/2))] gradient v) ∧
        ∀ h : ℝ, 0 < h → h < r/2 →
          |(v ((h : Plane)*Complex.I) - v 0)/h - (gradient v 0).im| ≤ C*M*h := by
  obtain ⟨A, hA, hlocal⟩ := exists_uniform_ball_harmonic_L2_constant hr
  let K : ℝ := (eLpNorm (fun z => fderiv ℝ (radialKernel r) z Complex.I) 2 volume).toReal
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  refine ⟨K*A+1, by positivity, ?_⟩
  intro E w g M hm hw hM hbound
  obtain ⟨v, hv, hAE, hG, hTaylor⟩ := hw.exists_smoothRepresentative_normal_quotient_bound hm hr
  refine ⟨v, hv, hAE, hG, ?_⟩
  intro h hh hhR
  apply (hTaylor h hh hhR).trans
  have hb := mul_le_mul_of_nonneg_left (hlocal hm hw hM hbound) hK
  change K * (eLpNorm ((Metric.ball (0 : Plane) (2*r)).indicator g) 2 volume).toReal ≤
    K * (A*M) at hb
  unfold harmonicNormalTaylorCoefficient
  change K * (eLpNorm ((Metric.ball (0 : Plane) (2*r)).indicator g) 2 volume).toReal * h ≤
    (K*A+1)*M*h
  nlinarith

end Torsion

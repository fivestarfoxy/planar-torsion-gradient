module

public import Torsion.Proof.PaperBrownianModel
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! # One-time Gaussian laws and covariance of standard planar Brownian motion -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Torsion.Brownian
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → Plane}

/-- The coordinates at any one time have independent centered Gaussian laws. -/
theorem IsPlanarBrownian.coordLaw (hB : IsPlanarBrownian B P) (t : ℝ≥0) :
    HasLaw (fun ω => ((B t ω).re, (B t ω).im))
      ((gaussianReal 0 t).prod (gaussianReal 0 t)) P := by
  let : IsProbabilityMeasure P := hB.re.isGaussianProcess.isProbabilityMeasure
  exact (hB.independent.comp (measurable_pi_apply t) (measurable_pi_apply t)).hasLaw_prod
    (hB.re.hasLaw_eval t) (hB.im.hasLaw_eval t)

/-- Brownian scaling at a fixed time in the actual planar joint law. -/
theorem IsPlanarBrownian.coordLaw_smul (hB : IsPlanarBrownian B P) (r : ℝ) :
    HasLaw (fun ω => (r*(B 1 ω).re, r*(B 1 ω).im))
      ((gaussianReal 0 ⟨r^2, sq_nonneg r⟩).prod (gaussianReal 0 ⟨r^2, sq_nonneg r⟩)) P := by
  let : IsProbabilityMeasure P := hB.re.isGaussianProcess.isProbabilityMeasure
  have hi := hB.independent.comp ((measurable_pi_apply (1:ℝ≥0)).const_mul r)
    ((measurable_pi_apply (1:ℝ≥0)).const_mul r)
  simpa only [mul_zero, mul_one] using! hi.hasLaw_prod
    (gaussianReal_const_mul (hB.re.hasLaw_eval 1) r) (gaussianReal_const_mul (hB.im.hasLaw_eval 1) r)

/-- Bounded-time expectations can be evaluated by rescaling the unit Gaussian.
The identity holds for every measurable real test. -/
theorem IsPlanarBrownian.integral_scaled (hB : IsPlanarBrownian B P) (r : ℝ)
    {f : Plane → ℝ} (hf : Measurable f) :
    (∫ ω, f (B ⟨r^2, sq_nonneg r⟩ ω) ∂P) = ∫ ω, f (r • B 1 ω) ∂P := by
  let g := f ∘ Complex.equivRealProdCLM.symm
  have hg : Measurable g := hf.comp Complex.equivRealProdCLM.symm.continuous.measurable
  have h1 := (hB.coordLaw ⟨r^2, sq_nonneg r⟩).integral_comp hg.aestronglyMeasurable
  have h2 := (hB.coordLaw_smul r).integral_comp hg.aestronglyMeasurable
  have he (z : ℂ) : Complex.equivRealProdCLM.symm (r*z.re, r*z.im) = r • z := by
    apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply, Complex.real_smul]
  have hi (z : ℂ) : Complex.equivRealProdCLM.symm (z.re, z.im) = z := Complex.equivRealProdCLM.symm_apply_apply z
  simpa only [g, Function.comp_apply, he, hi] using h1.trans h2.symm

private theorem coord_moments {X : ℝ≥0 → Ω → ℝ} (hX : IsBrownianReal X P) :
    (∫ ω, X 1 ω ^ 2 ∂P) = 1 := by
  have h := (hX.hasLaw_eval 1).variance_eq
  rw [variance_eq_integral (hX.aemeasurable 1), hX.integral_eval] at h
  simpa using h

/-- The covariance of the unit-time coordinates is the identity matrix. -/
theorem IsPlanarBrownian.unit_moments (hB : IsPlanarBrownian B P) :
    (∫ ω, (B 1 ω).re ^ 2 ∂P) = 1 ∧ (∫ ω, (B 1 ω).im ^ 2 ∂P) = 1 ∧
    (∫ ω, (B 1 ω).re * (B 1 ω).im ∂P) = 0 := by
  refine ⟨coord_moments hB.re, coord_moments hB.im, ?_⟩
  have hi := hB.independent.comp (measurable_pi_apply (1:ℝ≥0)) (measurable_pi_apply (1:ℝ≥0))
  have h := hi.integral_fun_mul_eq_mul_integral (hB.re.aemeasurable 1).aestronglyMeasurable
    (hB.im.aemeasurable 1).aestronglyMeasurable
  simpa only [Function.comp_apply, hB.re.integral_eval, hB.im.integral_eval, mul_zero] using h

/-- The norm squared of the unit-time Brownian sample is integrable. -/
theorem IsPlanarBrownian.integrable_sq_norm (hB : IsPlanarBrownian B P) :
    Integrable (fun ω => ‖B 1 ω‖ ^ 2) P := by
  have hr := (hB.re.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two.integrable_sq
  have hi := (hB.im.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two.integrable_sq
  simpa only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← sq, Pi.add_apply] using! hr.add hi

end Torsion.Brownian

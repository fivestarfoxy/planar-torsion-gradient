module

public import Torsion.Proof.PaperBrownianMoments
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! # The Gaussian Brownian generator on planar Fourier modes

Every frequency has the exact heat multiplier exp(-t |ξ|²/2). Its
right derivative at time zero is the Fourier symbol of one-half the
Euclidean Laplacian.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set ProbabilityTheory MeasureTheory Filter
open scoped Topology NNReal
namespace Torsion.Brownian
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → Plane}

/-- The projection onto any frequency vector ξ is a centered Gaussian of
variance t |ξ|², including zero frequency and time zero. -/
theorem IsPlanarBrownian.projectionLaw (hB : IsPlanarBrownian B P) (t : ℝ≥0) (ξ : Plane) :
    HasLaw (fun ω => inner ℝ ξ (B t ω)) (gaussianReal 0 (‖ξ‖₊ ^ 2 * t)) P := by
  let X := fun ω => ξ.re * (B t ω).re
  let Y := fun ω => ξ.im * (B t ω).im
  have hi : IndepFun X Y P := by
    simpa only [X, Y, Function.comp_def] using! hB.independent.comp ((measurable_pi_apply t).const_mul ξ.re)
      ((measurable_pi_apply t).const_mul ξ.im)
  have hX := gaussianReal_const_mul (hB.re.hasLaw_eval t) ξ.re
  have hY := gaussianReal_const_mul (hB.im.hasLaw_eval t) ξ.im
  have he : (fun ω => inner ℝ ξ (B t ω)) = X+Y := by
    funext ω
    simp [X, Y, Complex.inner, Complex.mul_re, mul_comm]
  rw [he]
  refine ⟨hX.aemeasurable.add hY.aemeasurable, ?_⟩
  rw [gaussianReal_add_gaussianReal_of_indepFun hi hX hY]
  congr 1
  · ring
  · apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_mk, coe_nnnorm,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring

/-- The exact Brownian heat multiplier at every planar frequency. -/
theorem IsPlanarBrownian.fourier_expectation (hB : IsPlanarBrownian B P) (t : ℝ≥0) (ξ : Plane) :
    (∫ ω, Complex.exp ((inner ℝ ξ (B t ω) : ℂ)*Complex.I) ∂P) =
      Complex.exp (-((‖ξ‖ ^ 2 : ℝ) : ℂ) * (t : ℝ) / 2) := by
  have hl := hB.projectionLaw t ξ
  have h := hl.integral_comp (f := fun y : ℝ => Complex.exp ((y : ℂ)*Complex.I)) (by fun_prop)
  simp only [Function.comp_apply] at h
  rw [h]
  have hc := charFun_gaussianReal (μ := 0) (v := ‖ξ‖₊^2*t) 1
  rw [charFun_apply_real] at hc
  simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, one_mul, one_pow, mul_one, zero_sub,
    NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm, Complex.ofReal_mul, Complex.ofReal_pow] at hc ⊢
  convert hc using 2
  ring

/-- The right infinitesimal generator of standard planar Brownian motion on
the mode exp(i〈ξ,x〉), evaluated at the origin. -/
theorem IsPlanarBrownian.fourier_generator (hB : IsPlanarBrownian B P) (ξ : Plane) :
    HasDerivWithinAt (fun s : ℝ =>
      ∫ ω, Complex.exp ((inner ℝ ξ (B s.toNNReal ω) : ℂ)*Complex.I) ∂P)
      (-((‖ξ‖^2 : ℝ) : ℂ) / 2) (Ici 0) 0 := by
  let a : ℂ := -((‖ξ‖^2 : ℝ) : ℂ) / 2
  have hc : HasDerivAt (fun z : ℂ => Complex.exp (a*z)) a ((0:ℝ):ℂ) := by
    simpa [Function.comp_def] using (Complex.hasDerivAt_exp (a*((0:ℝ):ℂ))).comp ((0:ℝ):ℂ)
      ((hasDerivAt_id ((0:ℝ):ℂ)).const_mul a)
  have h := hc.comp_ofReal
  refine h.hasDerivWithinAt.congr (fun s hs => ?_) ?_
  · rw [hB.fourier_expectation, Real.coe_toNNReal s hs]
    congr 1
    dsimp [a]
    ring
  · rw [hB.fourier_expectation]
    simp

/-- The same generator at every starting point, with the actual translated
Brownian path in the expectation. -/
theorem IsPlanarBrownian.translated_fourier_generator (hB : IsPlanarBrownian B P) (x ξ : Plane) :
    HasDerivWithinAt (fun s : ℝ => ∫ ω,
      Complex.exp ((inner ℝ ξ (x + B s.toNNReal ω) : ℂ)*Complex.I) ∂P)
      (Complex.exp ((inner ℝ ξ x : ℂ)*Complex.I) * (-((‖ξ‖^2 : ℝ) : ℂ)/2)) (Ici 0) 0 := by
  have he (s : ℝ) :
      (∫ ω, Complex.exp ((inner ℝ ξ (x + B s.toNNReal ω) : ℂ)*Complex.I) ∂P) =
        Complex.exp ((inner ℝ ξ x : ℂ)*Complex.I) *
        ∫ ω, Complex.exp ((inner ℝ ξ (B s.toNNReal ω) : ℂ)*Complex.I) ∂P := by
    simp only [inner_add_right, Complex.ofReal_add, add_mul, Complex.exp_add, integral_const_mul]
  simpa only [he] using (hB.fourier_generator ξ).const_mul (Complex.exp ((inner ℝ ξ x : ℂ)*Complex.I))

end Torsion.Brownian

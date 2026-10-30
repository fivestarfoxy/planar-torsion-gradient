import Torsion.CauchyTransform
import Torsion.CauchyTransformHeightDerivative
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Integration by parts for the concrete Cauchy transform

The derivative kernel can be transferred from `Y` to its derivative `-φ`.
The proof includes the vanishing boundary terms at both support endpoints.
-/

noncomputable section
open Set MeasureTheory

namespace Torsion.Spectral

private theorem denominator_ne_zero {z : ℂ} (hz : z ∈ upperHalfPlane) (s : ℝ) :
    z - (s : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
  exact hz.ne' hi

/-- Integration by parts for a general real C¹ density vanishing at the
support endpoints. Its derivative is supplied by ordinary derivative proofs. -/
theorem cauchy_integrationByParts_of_hasDerivAt {f fp : ℝ → ℝ}
    (hf : Continuous f) (hfp : Continuous fp)
    (hd : ∀ s : ℝ, HasDerivAt f (fp s) s) (hm : f (-1) = 0) (hp : f 1 = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (∫ s in Icc (-1 : ℝ) 1, (f s : ℂ) / (z - (s : ℂ)) ^ 2) =
      -(∫ s in Icc (-1 : ℝ) 1, (fp s : ℂ) / (z - (s : ℂ))) := by
  let g : ℝ → ℂ := fun s => (f s : ℂ) / (z - (s : ℂ))
  let gp : ℝ → ℂ := fun s => (fp s : ℂ) / (z - (s : ℂ)) +
    (f s : ℂ) / (z - (s : ℂ)) ^ 2
  have hden : Continuous (fun s : ℝ => z - (s : ℂ)) :=
    continuous_const.sub Complex.continuous_ofReal
  have hfc : Continuous (fun s : ℝ => (f s : ℂ)) := Complex.continuous_ofReal.comp hf
  have hfpc : Continuous (fun s : ℝ => (fp s : ℂ)) := Complex.continuous_ofReal.comp hfp
  have hkfp : Continuous (fun s : ℝ => (fp s : ℂ) / (z - (s : ℂ))) :=
    hfpc.div hden (denominator_ne_zero hz)
  have hkf : Continuous (fun s : ℝ => (f s : ℂ) / (z - (s : ℂ)) ^ 2) :=
    hfc.div (hden.pow 2) (fun s => pow_ne_zero 2 (denominator_ne_zero hz s))
  have hgp : Continuous gp := hkfp.add hkf
  have hderiv : ∀ s : ℝ, HasDerivAt g (gp s) s := by
    intro s
    have hn := (hd s).ofReal_comp
    have hden' := (hasDerivAt_const s z).sub (Complex.ofRealCLM.hasDerivAt (x := s))
    have h := hn.div hden' (denominator_ne_zero hz s)
    convert h using 1
    dsimp [g, gp]
    field_simp [denominator_ne_zero hz s]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) (hgp.intervalIntegrable (-1) 1)
  simp only [g, hp, hm, Complex.ofReal_zero, zero_div, sub_self] at hi
  have hieq : (∫ s in (-1 : ℝ)..1, (fp s : ℂ) / (z - (s : ℂ))) +
      (∫ s in (-1 : ℝ)..1, (f s : ℂ) / (z - (s : ℂ)) ^ 2) = 0 := by
    simpa only [gp, intervalIntegral.integral_add
      (hkfp.intervalIntegrable (-1) 1) (hkf.intervalIntegrable (-1) 1)] using hi
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  linear_combination hieq

/-- The integration-by-parts kernel identity underlying `(CY)' = C(Y')`. -/
theorem cauchy_height_integrationByParts {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (∫ s in Icc (-1 : ℝ) 1, (height φ s : ℂ) / (z - (s : ℂ)) ^ 2) =
      ∫ s in Icc (-1 : ℝ) 1, (φ s : ℂ) / (z - (s : ℂ)) := by
  let g : ℝ → ℂ := fun s => (height φ s : ℂ) / (z - (s : ℂ))
  let gp : ℝ → ℂ := fun s => -(φ s : ℂ) / (z - (s : ℂ)) +
    (height φ s : ℂ) / (z - (s : ℂ)) ^ 2
  have hden : Continuous (fun s : ℝ => z - (s : ℂ)) :=
    continuous_const.sub Complex.continuous_ofReal
  have hφc : Continuous (fun s : ℝ => (φ s : ℂ)) := Complex.continuous_ofReal.comp hφ
  have hYc : Continuous (fun s : ℝ => (height φ s : ℂ)) :=
    Complex.continuous_ofReal.comp (height_continuous hφ.continuousOn)
  have hkφ : Continuous (fun s : ℝ => (φ s : ℂ) / (z - (s : ℂ))) :=
    hφc.div hden (denominator_ne_zero hz)
  have hkY : Continuous (fun s : ℝ => (height φ s : ℂ) / (z - (s : ℂ)) ^ 2) :=
    hYc.div (hden.pow 2) (fun s => pow_ne_zero 2 (denominator_ne_zero hz s))
  have hgp : Continuous gp := by
    simpa only [gp, neg_div] using hkφ.neg.add hkY
  have hderiv : ∀ s : ℝ, HasDerivAt g (gp s) s := by
    intro s
    have hn := (hasDerivAt_height hφ hodd hzero s).ofReal_comp
    have hd := (hasDerivAt_const s z).sub (Complex.ofRealCLM.hasDerivAt (x := s))
    have h := hn.div hd (denominator_ne_zero hz s)
    convert h using 1
    dsimp [g, gp]
    push_cast
    field_simp [denominator_ne_zero hz s]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) (hgp.intervalIntegrable (-1) 1)
  have hY₁ : height φ (1 : ℝ) = 0 := height_zero_of_one_le_abs φ (by norm_num)
  have hYm : height φ (-1 : ℝ) = 0 := height_zero_of_one_le_abs φ (by norm_num)
  simp only [g, hY₁, hYm, Complex.ofReal_zero, zero_div, sub_self] at hi
  have hieq : -(∫ s in (-1 : ℝ)..1, (φ s : ℂ) / (z - (s : ℂ))) +
      (∫ s in (-1 : ℝ)..1, (height φ s : ℂ) / (z - (s : ℂ)) ^ 2) = 0 := by
    simpa only [gp, neg_div, intervalIntegral.integral_add
      (hkφ.neg.intervalIntegrable (-1) 1) (hkY.intervalIntegrable (-1) 1), intervalIntegral.integral_neg] using hi
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  linear_combination hieq

/-- Interior derivative formula expressed directly in terms of the original
odd eigenfunction, rather than its integrated height profile. -/
theorem deriv_cauchy_eq_eigenfunction_integral {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    deriv (cauchy φ) z = (Real.pi : ℂ)⁻¹ *
      ∫ s in Icc (-1 : ℝ) 1, (φ s : ℂ) / (z - (s : ℂ)) := by
  rw [deriv_cauchy_eq hφ.continuousOn hz,
    cauchy_height_integrationByParts hφ hodd hzero hz]

/-- The derivative of the auxiliary transform in terms of the product Yφ.
This is the interior identity whose imaginary trace is -Yφ = YY'. -/
theorem deriv_auxiliary_eq_product_integral {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    deriv (auxiliary φ) z = (Real.pi : ℂ)⁻¹ *
      ∫ s in Icc (-1 : ℝ) 1, ((height φ s * φ s : ℝ) : ℂ) / (z - (s : ℂ)) := by
  have hY := height_continuous hφ.continuousOn
  have hd : ∀ s : ℝ, HasDerivAt (fun s => (height φ s) ^ 2)
      (-2 * (height φ s * φ s)) s := by
    intro s
    convert (hasDerivAt_height hφ hodd hzero s).pow 2 using 1
    ring
  have hi := cauchy_integrationByParts_of_hasDerivAt (hY.pow 2)
    (continuous_const.mul (hY.mul hφ)) hd
    (by rw [height_zero_of_one_le_abs φ (by norm_num)]; norm_num)
    (by rw [height_zero_of_one_le_abs φ (by norm_num)]; norm_num) hz
  rw [deriv_auxiliary_eq hφ.continuousOn hz, hi]
  push_cast
  simp only [mul_div_assoc, integral_const_mul, mul_inv_rev]
  ring

end Torsion.Spectral

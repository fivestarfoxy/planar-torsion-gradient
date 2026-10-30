module

public import Torsion.RestrictedSpectralPrimitive
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The damped Hilbert Fourier multiplier

The multiplier `i sign ξ exp(-y|ξ|)` has the actual inverse Fourier kernel
`-2t/(t²+y²)`. The value at frequency zero is immaterial to the integrals.
All integrals at positive height are absolutely convergent.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- Source-normalized conjugate-Poisson Fourier multiplier. Its arbitrary
value at zero avoids a second case in the positive/negative frequency split. -/
def dampedSignMultiplier (y ξ : ℝ) : ℂ :=
  (Real.exp (-y * |ξ|) : ℂ) * (if 0 < ξ then Complex.I else -Complex.I)

@[simp] theorem norm_dampedSignMultiplier (y ξ : ℝ) :
    ‖dampedSignMultiplier y ξ‖ = Real.exp (-y * |ξ|) := by
  unfold dampedSignMultiplier
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  split_ifs <;> simp

/-- Positive and negative frequency branches are ordinary exponentially
integrable functions at every positive height. -/
theorem integrable_dampedSignMultiplier {y : ℝ} (hy : 0 < y) :
    Integrable (dampedSignMultiplier y) := by
  have hi : IntegrableOn (dampedSignMultiplier y) (Iic (0 : ℝ)) := by
    have h := (integrableOn_exp_mul_complex_Iic
      (a := (y : ℂ)) (by simpa using hy) 0).mul_const (-Complex.I)
    apply IntegrableOn.congr_fun h _ measurableSet_Iic
    intro ξ hξ
    simp only [mem_Iic] at hξ
    simp only [dampedSignMultiplier, not_lt_of_ge hξ, if_false, abs_of_nonpos hξ]
    rw [Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  have hj : IntegrableOn (dampedSignMultiplier y) (Ioi (0 : ℝ)) := by
    have h := (integrableOn_exp_mul_complex_Ioi
      (a := (-y : ℝ)) (by simpa using neg_neg_of_pos hy) 0).mul_const Complex.I
    apply IntegrableOn.congr_fun h _ measurableSet_Ioi
    intro ξ hξ
    simp only [mem_Ioi] at hξ
    simp only [dampedSignMultiplier, hξ, if_true, abs_of_pos hξ]
    rw [Complex.ofReal_exp]
    congr 2
    push_cast
    rfl
  have h := hi.union hj
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

/-- The damped multiplier is integrable after multiplication by a real
Fourier phase, since that phase has modulus one. -/
theorem integrable_dampedSignMultiplier_phase {y : ℝ} (hy : 0 < y) (t : ℝ) :
    Integrable (fun ξ : ℝ => dampedSignMultiplier y ξ *
      Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I)) := by
  apply ((integrable_dampedSignMultiplier hy).norm).mono'
  · apply Measurable.aestronglyMeasurable
    have hm : Measurable (fun ξ : ℝ => if 0 < ξ then Complex.I else -Complex.I) :=
      Measurable.ite measurableSet_Ioi measurable_const measurable_const
    exact (((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_abs))).measurable).mul hm).mul
        (by fun_prop)
  · exact ae_of_all _ fun ξ => by
      simp [norm_mul, Complex.norm_exp]

/-- Actual inverse Fourier kernel, before the source's factor `1/(2π)`. -/
theorem integral_dampedSignMultiplier_phase {y : ℝ} (hy : 0 < y) (t : ℝ) :
    (∫ ξ : ℝ, dampedSignMultiplier y ξ *
      Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I)) =
      ((-2 * t / (t ^ 2 + y ^ 2) : ℝ) : ℂ) := by
  let p : ℂ := (y : ℂ) + (t : ℂ) * Complex.I
  let q : ℂ := -(y : ℂ) + (t : ℂ) * Complex.I
  have hp : 0 < p.re := by simpa [p] using hy
  have hq : q.re < 0 := by simpa [q] using neg_neg_of_pos hy
  have hleft :
      (∫ ξ : ℝ in Iic 0, dampedSignMultiplier y ξ *
        Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I)) =
          (-Complex.I) * (1 / p) := by
    calc
      _ = ∫ ξ : ℝ in Iic 0, (-Complex.I) * Complex.exp (p * ξ) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro ξ hξ
        change ξ ≤ 0 at hξ
        have hn : ¬ 0 < ξ := not_lt_of_ge hξ
        simp only [dampedSignMultiplier, hn, if_false, abs_of_nonpos hξ]
        rw [Complex.ofReal_exp]
        calc
          _ = (-Complex.I) * (Complex.exp (((-y * -ξ : ℝ) : ℂ)) *
              Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I)) := by ring
          _ = (-Complex.I) * Complex.exp (((-y * -ξ : ℝ) : ℂ) +
              ((t * ξ : ℝ) : ℂ) * Complex.I) := by rw [← Complex.exp_add]
          _ = _ := by
            congr 2
            dsimp [p]
            push_cast
            ring
      _ = (-Complex.I) * (1 / p) := by
        rw [integral_const_mul, integral_exp_mul_complex_Iic hp]
        simp
  have hright :
      (∫ ξ : ℝ in Ioi 0, dampedSignMultiplier y ξ *
        Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I)) =
          Complex.I * (-1 / q) := by
    calc
      _ = ∫ ξ : ℝ in Ioi 0, Complex.I * Complex.exp (q * ξ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro ξ hξ
        change 0 < ξ at hξ
        simp only [dampedSignMultiplier, hξ, if_true, abs_of_pos hξ]
        rw [Complex.ofReal_exp]
        calc
          _ = Complex.I * (Complex.exp (((-y * ξ : ℝ) : ℂ)) *
              Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I)) := by ring
          _ = Complex.I * Complex.exp (((-y * ξ : ℝ) : ℂ) +
              ((t * ξ : ℝ) : ℂ) * Complex.I) := by rw [← Complex.exp_add]
          _ = _ := by
            congr 2
            dsimp [q]
            push_cast
            ring
      _ = Complex.I * (-1 / q) := by
        rw [integral_const_mul, integral_exp_mul_complex_Ioi hq]
        simp
  have hint := integrable_dampedSignMultiplier_phase hy t
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn,
    hleft, hright]
  have hpne : p ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hqne : q ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hden : (t : ℂ) ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by
    have hreal : 0 < t ^ 2 + y ^ 2 := by positivity
    exact_mod_cast hreal.ne'
  push_cast
  dsimp [p, q] at *
  field_simp [hpne, hqne, hden]
  ring_nf
  have hpne' : Complex.I * (t : ℂ) + (y : ℂ) ≠ 0 := by
    simpa only [add_comm, mul_comm] using hpne
  have hqne' : Complex.I * (t : ℂ) - (y : ℂ) ≠ 0 := by
    simpa only [sub_eq_add_neg, add_comm, mul_comm] using hqne
  field_simp [hpne', hqne']
  ring_nf
  all_goals try simp [Complex.I_sq]
  all_goals ring

end Torsion.Spectral

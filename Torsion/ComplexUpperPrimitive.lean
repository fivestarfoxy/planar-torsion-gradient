import Torsion.ComplexPrimitives
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A continuous primitive up to the boundary of the upper half-plane. -/
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology Interval

namespace Torsion.ComplexReflection

/-- Retraction onto the actual closed upper half-plane. -/
def upperClamp (z : ℂ) : ℂ := z.re + max z.im 0 * I

lemma upperClamp_continuous : Continuous upperClamp := by
  unfold upperClamp
  fun_prop

lemma upperClamp_mem (z : ℂ) : 0 ≤ (upperClamp z).im := by
  simp [upperClamp]

lemma upperClamp_eq {z : ℂ} (hz : 0 ≤ z.im) : upperClamp z = z := by
  simp only [upperClamp, max_eq_left hz, re_add_im]

lemma continuous_comp_upperClamp {f : ℂ → ℂ}
    (hf : ContinuousOn f {z : ℂ | 0 ≤ z.im}) : Continuous (f ∘ upperClamp) := by
  exact hf.comp_continuous upperClamp_continuous upperClamp_mem

/-- A concrete horizontal-then-vertical primitive, with a continuous
retraction making it defined continuously on the whole plane. -/
def upperPrimitive (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  wedgeIntegral 0 z (f ∘ upperClamp)

lemma upperPrimitive_continuous {f : ℂ → ℂ}
    (hf : ContinuousOn f {z : ℂ | 0 ≤ z.im}) : Continuous (upperPrimitive f) := by
  have hg := continuous_comp_upperClamp hf
  unfold upperPrimitive wedgeIntegral
  simp only [zero_re, zero_im, ofReal_zero, zero_mul, add_zero]
  apply Continuous.add
  · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact hg.comp (Complex.continuous_ofReal.comp continuous_snd)
    · exact Complex.continuous_re
  · apply continuous_const.smul
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact hg.comp (by fun_prop : Continuous (fun p : ℂ × ℝ => p.1.re + p.2 * I))
    · exact Complex.continuous_im

private lemma wedgePrimitive_sub {g : ℂ → ℂ} (hg : Continuous g)
    (hd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ g z)
    {z : ℂ} (hz : 0 < z.im) (w : ℂ) :
    wedgeIntegral 0 w g - wedgeIntegral 0 z g = wedgeIntegral z w g := by
  let I₁ := ∫ x in (0 : ℝ)..w.re, g (x : ℂ)
  let I₂ := I • ∫ y in (0 : ℝ)..w.im, g (w.re + y * I)
  let I₃ := ∫ x in (0 : ℝ)..z.re, g (x : ℂ)
  let I₄ := I • ∫ y in (0 : ℝ)..z.im, g (z.re + y * I)
  let I₅ := ∫ x in z.re..w.re, g (x + z.im * I)
  let I₆ := I • ∫ y in z.im..w.im, g (w.re + y * I)
  let I₇ := ∫ x in z.re..w.re, g (x : ℂ)
  let I₈ := I • ∫ y in (0 : ℝ)..z.im, g (w.re + y * I)
  have hiH : Continuous (fun x : ℝ => g (x : ℂ)) := hg.comp continuous_ofReal
  have hiV (r : ℝ) : Continuous (fun y : ℝ => g (r + y * I)) := hg.comp (by fun_prop)
  have hI₁ : I₁ = I₃ + I₇ :=
    (intervalIntegral.integral_add_adjacent_intervals (hiH.intervalIntegrable _ _)
      (hiH.intervalIntegrable _ _)).symm
  have hI₂ : I₂ = I₈ + I₆ := by
    dsimp only [I₂, I₈, I₆]
    rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals
      ((hiV w.re).intervalIntegrable _ _) ((hiV w.re).intervalIntegrable _ _)]
  have hI₀ : I₇ - I₅ + I₈ - I₄ = 0 := by
    have h := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn g
      (z.re : ℂ) (w.re + z.im * I) hg.continuousOn (fun u hu => ?_)
    · simpa only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im,
        ofReal_re, ofReal_im, mul_zero, zero_mul, sub_zero, mul_one, add_zero, zero_add,
        ofReal_zero, zero_smul] using h
    · apply (hd u ?_).differentiableWithinAt
      have hi := hu.2.1
      simpa only [ofReal_im, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im,
        I_re, mul_zero, add_zero, zero_add, min_eq_left hz.le] using hi
  simp only [wedgeIntegral, zero_re, zero_im, ofReal_zero, zero_mul, add_zero]
  change I₁ + I₂ - (I₃ + I₄) = I₅ + I₆
  rw [hI₁, hI₂]
  calc
    (I₃ + I₇) + (I₈ + I₆) - (I₃ + I₄) = (I₇ - I₅ + I₈ - I₄) + (I₅ + I₆) := by abel
    _ = I₅ + I₆ := by rw [hI₀, zero_add]

/-- The concrete primitive differentiates to the original function at
all upper half-plane points. -/
theorem upperPrimitive_hasDerivAt {f : ℂ → ℂ}
    (hf : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    {z : ℂ} (hz : 0 < z.im) : HasDerivAt (upperPrimitive f) (f z) z := by
  let g : ℂ → ℂ := f ∘ upperClamp
  have hg : Continuous g := continuous_comp_upperClamp hf
  have hfg : EqOn g f {z : ℂ | 0 < z.im} := fun w hw => by simp [g, upperClamp_eq hw.le]
  have hgd : DifferentiableOn ℂ g {z : ℂ | 0 < z.im} := hd.congr hfg
  have hgdAt (w : ℂ) (hw : 0 < w.im) : DifferentiableAt ℂ g w :=
    (hgd w hw).differentiableAt ((isOpen_lt continuous_const continuous_im).mem_nhds hw)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const continuous_im) z hz
  have hdB : DifferentiableOn ℂ g (Metric.ball z r) := hgd.mono hball
  have hQ := hdB.isConservativeOn.hasDerivAt_wedgeIntegral hdB.continuousOn (Metric.mem_ball_self hr)
  have hP : HasDerivAt (fun w => wedgeIntegral z w g + wedgeIntegral 0 z g) (g z) z :=
    hQ.add_const _
  rw [hfg hz] at hP
  apply hP.congr_of_eventuallyEq
  filter_upwards [] with w
  dsimp only [upperPrimitive]
  change wedgeIntegral 0 w g = wedgeIntegral z w g + wedgeIntegral 0 z g
  exact sub_eq_iff_eq_add.mp (wedgePrimitive_sub hg hgdAt hz w)

/-- On the real line the concrete primitive is exactly the ordinary
integral of the continuous boundary datum. -/
theorem upperPrimitive_ofReal (f : ℂ → ℂ) (t : ℝ) :
    upperPrimitive f (t : ℂ) = ∫ x in (0 : ℝ)..t, f (x : ℂ) := by
  simp [upperPrimitive, wedgeIntegral, upperClamp]

/-- The boundary restriction of the concrete primitive has its classical
real derivative equal to the original continuous boundary datum. -/
theorem upperPrimitive_boundary_hasDerivAt {f : ℂ → ℂ}
    (hf : ContinuousOn f {z : ℂ | 0 ≤ z.im}) (t : ℝ) :
    HasDerivAt (fun x : ℝ => upperPrimitive f (x : ℂ)) (f (t : ℂ)) t := by
  have hc : Continuous (fun x : ℝ => f (x : ℂ)) :=
    hf.comp_continuous continuous_ofReal (by intro x; simp)
  simpa only [upperPrimitive_ofReal] using
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt

end Torsion.ComplexReflection

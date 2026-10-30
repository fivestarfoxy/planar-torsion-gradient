import Torsion.CauchyImageAreaBoundary
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Rectangle exhaustion of the actual Cauchy Jacobian energy

The half-open parameter rectangles increase to the open upper half-plane.
Their ordinary iterated interval integrals converge to the genuine Euclidean
area of the Cauchy image, by the actual Jacobian identity and integrability.
The half-open convention also avoids introducing any artificial boundary
integrability assumption on the real axis.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal Interval

namespace Torsion.Spectral

/-- A half-open rectangle in the parameter half-plane. -/
def cauchyAreaRectangle (R : ℝ) : Set ℂ := Ioc (-R) R ×ℂ Ioc 0 R

theorem cauchyAreaRectangle_measurableSet (R : ℝ) :
    MeasurableSet (cauchyAreaRectangle R) :=
  (measurableSet_Ioc.preimage Complex.continuous_re.measurable).inter
    (measurableSet_Ioc.preimage Complex.continuous_im.measurable)

theorem cauchyAreaRectangle_subset (R : ℝ) :
    cauchyAreaRectangle R ⊆ upperHalfPlane := by
  intro z hz
  exact hz.2.1

/-- The natural increasing rectangles cover the entire open half-plane. -/
theorem iUnion_cauchyAreaRectangle :
    (⋃ n : ℕ, cauchyAreaRectangle ((n : ℝ) + 2)) = upperHalfPlane := by
  apply Subset.antisymm
  · exact iUnion_subset fun n => cauchyAreaRectangle_subset _
  · intro z hz
    obtain ⟨n, hn⟩ := exists_nat_gt (max |z.re| z.im)
    refine mem_iUnion.mpr ⟨n, ?_⟩
    have hx := (le_max_left |z.re| z.im).trans_lt hn
    have hy := (le_max_right |z.re| z.im).trans_lt hn
    have hneg := neg_le_abs z.re
    have hpos := le_abs_self z.re
    change (-((n : ℝ) + 2) < z.re ∧ z.re ≤ (n : ℝ) + 2) ∧
      (0 < z.im ∧ z.im ≤ (n : ℝ) + 2)
    exact ⟨⟨by linarith, by linarith⟩, ⟨hz, by linarith⟩⟩

theorem cauchyAreaRectangle_monotone :
    Monotone (fun n : ℕ => cauchyAreaRectangle ((n : ℝ) + 2)) := by
  intro n m hnm z hz
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  change (-((m : ℝ) + 2) < z.re ∧ z.re ≤ (m : ℝ) + 2) ∧
    (0 < z.im ∧ z.im ≤ (m : ℝ) + 2)
  change (-((n : ℝ) + 2) < z.re ∧ z.re ≤ (n : ℝ) + 2) ∧
    (0 < z.im ∧ z.im ≤ (n : ℝ) + 2) at hz
  exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
    ⟨hz.2.1, by linarith [hz.2.2]⟩⟩

/-- Integrable half-plane functions admit the actual increasing rectangle
exhaustion, without any boundary values or differentiability hypotheses. -/
theorem integral_cauchyAreaRectangle_tendsto {f : ℂ → ℝ}
    (hf : IntegrableOn f upperHalfPlane) :
    Tendsto (fun n : ℕ => ∫ z in cauchyAreaRectangle ((n : ℝ) + 2), f z)
      atTop (𝓝 (∫ z in upperHalfPlane, f z)) := by
  have hfi : IntegrableOn f (⋃ n : ℕ, cauchyAreaRectangle ((n : ℝ) + 2)) := by
    rwa [iUnion_cauchyAreaRectangle]
  simpa only [iUnion_cauchyAreaRectangle] using
    tendsto_setIntegral_of_monotone (fun n => cauchyAreaRectangle_measurableSet _)
      cauchyAreaRectangle_monotone hfi

/-- Product-coordinate change of variables on the concrete complex
rectangle, with ordinary interval-integral conventions. -/
theorem integral_cauchyAreaRectangle_eq_iterated {f : ℂ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hf : IntegrableOn f (cauchyAreaRectangle R)) :
    (∫ z in cauchyAreaRectangle R, f z) =
      ∫ x : ℝ in -R..R, ∫ y : ℝ in (0 : ℝ)..R,
        f ((x : ℂ) + (y : ℂ) * Complex.I) := by
  let e := Complex.measurableEquivRealProd.symm
  have hMP : MeasurePreserving e volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm
  have hpre : e ⁻¹' cauchyAreaRectangle R = Ioc (-R) R ×ˢ Ioc 0 R := rfl
  have hprod : IntegrableOn (f ∘ e) (Ioc (-R) R ×ˢ Ioc 0 R)
      ((volume : Measure ℝ).prod volume) := by
    have h := (hMP.integrableOn_comp_preimage e.measurableEmbedding).mpr hf
    simpa only [hpre, Measure.volume_eq_prod] using h
  have heq := (hMP.restrict_preimage (cauchyAreaRectangle_measurableSet R)).integral_comp
    e.measurableEmbedding f
  rw [hpre, Measure.volume_eq_prod] at heq
  change (∫ p in Ioc (-R) R ×ˢ Ioc 0 R, (f ∘ e) p
    ∂(volume : Measure ℝ).prod volume) = _ at heq
  rw [setIntegral_prod _ hprod] at heq
  rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  simp_rw [intervalIntegral.integral_of_le hR]
  convert heq.symm using 1
  congr 1
  funext x
  congr 1
  funext y
  apply congrArg f
  apply Complex.ext <;> simp [e]

/-- The actual continuous derivative extension has the same finite
half-plane energy as the holomorphic derivative. -/
theorem cauchyDerivativeExtension_sq_integrableOn {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    IntegrableOn (fun z => ‖cauchyDerivativeExtension φ z‖ ^ 2) upperHalfPlane := by
  apply (cauchy_deriv_sq_integrableOn hφ hodd hzero hpos).congr
  filter_upwards [ae_restrict_mem
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet] with z hz
  rw [cauchyDerivativeExtension_eq hφ hodd hzero hz]

/-- The rectangle Jacobian energies appearing in the proved Green identity
converge to the Euclidean area of the actual Cauchy image. -/
theorem cauchy_rectangle_energy_tendsto_area {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in -((n : ℝ) + 2)..((n : ℝ) + 2),
      ∫ y : ℝ in (0 : ℝ)..((n : ℝ) + 2),
        ‖cauchyDerivativeExtension φ ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)
      atTop (𝓝 ((volume (cauchyImage φ)).toReal)) := by
  have hf := cauchyDerivativeExtension_sq_integrableOn hφ hodd hzero hpos
  have heq : (∫ z in upperHalfPlane, ‖cauchyDerivativeExtension φ z‖ ^ 2) =
      (volume (cauchyImage φ)).toReal := by
    rw [area_cauchyImage_eq_integral_deriv_sq hφ hodd hzero hpos]
    apply setIntegral_congr_fun (isOpen_lt continuous_const Complex.continuous_im).measurableSet
    intro z hz
    dsimp only
    rw [cauchyDerivativeExtension_eq hφ hodd hzero hz]
  rw [← heq]
  apply (integral_cauchyAreaRectangle_tendsto hf).congr'
  exact Eventually.of_forall fun n =>
    integral_cauchyAreaRectangle_eq_iterated (by positivity)
      (hf.mono_set (cauchyAreaRectangle_subset _))

end Torsion.Spectral

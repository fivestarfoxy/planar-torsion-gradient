import Torsion.Definitions
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Dominated L² convergence for bounded Sobolev chain-rule coefficients

All statements apply to arbitrary measure spaces and real normed targets.
The coefficient bounds are almost-everywhere bounds, and the convergence
is genuine convergence in the concrete `eLpNorm` used by `MemH10`.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded measurable coefficient preserves Lᵖ membership. -/
theorem memLp_bounded_coeff_smul {a : X → ℝ} {g : X → E} {p : ℝ≥0∞} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hg : MemLp g p μ)
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) : MemLp (fun x => a x • g x) p μ := by
  apply hg.of_le_mul (ha.smul hg.1)
  filter_upwards [hb] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

omit [NormedSpace ℝ E] in
/-- Dominated pointwise convergence implies L² convergence, stated for the
actual seminorm rather than an abstract L² representative. -/
theorem tendsto_eLpNorm_two_of_dominated {F : ℕ → X → E} {B : X → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hB : Integrable (fun x => (B x) ^ 2) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ B x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 μ) atTop (𝓝 0) := by
  have hdom (n : ℕ) : ∀ᵐ x ∂μ, ‖‖F n x‖ ^ 2‖ ≤ (B x) ^ 2 := by
    filter_upwards [hb n] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hn := norm_nonneg (F n x)
    nlinarith
  have hsq (n : ℕ) : Integrable (fun x => ‖F n x‖ ^ 2) μ :=
    hB.mono' ((hF n).norm.pow 2) (hdom n)
  have hmem (n : ℕ) : MemLp (F n) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (hF n)).2 (hsq n)
  have hlimsq : ∀ᵐ x ∂μ, Tendsto (fun n => ‖F n x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using hx.norm.pow 2
  have hint : Tendsto (fun n => ∫ x, ‖F n x‖ ^ 2 ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence (fun x => (B x) ^ 2)
        (fun n => (hF n).norm.pow 2) hB hdom hlimsq
  have hn (n : ℕ) : eLpNorm (F n) 2 μ =
      ENNReal.ofReal (Real.sqrt (∫ x, ‖F n x‖ ^ 2 ∂μ)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow, one_div] using
      MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hmem n)
  simp_rw [hn]
  simpa only [Real.sqrt_zero, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto (Real.sqrt 0)).comp
      ((Real.continuous_sqrt.tendsto 0).comp hint)

/-- Almost-everywhere convergence of uniformly bounded coefficients gives L²
convergence after multiplication by a fixed L² vector field. -/
theorem tendsto_eLpNorm_bounded_coeff_smul {an : ℕ → X → ℝ} {a : X → ℝ}
    {g : X → E} {C : ℝ}
    (han : ∀ n, AEStronglyMeasurable (an n) μ)
    (ha : AEStronglyMeasurable a μ) (hg : MemLp g 2 μ)
    (hbn : ∀ n, ∀ᵐ x ∂μ, ‖an n x‖ ≤ C)
    (hba : ∀ᵐ x ∂μ, ‖a x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => an n x) atTop (𝓝 (a x))) :
    Tendsto (fun n => eLpNorm (fun x => (an n x - a x) • g x) 2 μ) atTop (𝓝 0) := by
  have hgsq : Integrable (fun x => ‖g x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  apply tendsto_eLpNorm_two_of_dominated
    (B := fun x => (2 * |C|) * ‖g x‖)
  · intro n
    exact ((han n).sub ha).smul hg.1
  · convert hgsq.const_mul ((2 * |C|) ^ 2) using 1
    funext x
    ring
  · intro n
    filter_upwards [hbn n, hba] with x hn hx
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖an n x - a x‖ ≤ ‖an n x‖ + ‖a x‖ := norm_sub_le _ _
      _ ≤ 2 * |C| := by linarith [le_abs_self C]
  · filter_upwards [hlim] with x hx
    simpa only [sub_self, zero_smul] using (hx.sub_const (a x)).smul_const (g x)

/-- Joint L² convergence of a bounded coefficient and an L²-convergent vector
field; this is the product passage in the Sobolev chain rule. -/
theorem tendsto_eLpNorm_bounded_coeff_smul_joint
    {an : ℕ → X → ℝ} {a : X → ℝ} {gn : ℕ → X → E} {g : X → E} {C : ℝ}
    (han : ∀ n, AEStronglyMeasurable (an n) μ)
    (ha : AEStronglyMeasurable a μ)
    (hgn : ∀ n, MemLp (gn n) 2 μ) (hg : MemLp g 2 μ)
    (hbn : ∀ n, ∀ᵐ x ∂μ, ‖an n x‖ ≤ C)
    (hba : ∀ᵐ x ∂μ, ‖a x‖ ≤ C)
    (halim : ∀ᵐ x ∂μ, Tendsto (fun n => an n x) atTop (𝓝 (a x)))
    (hglim : Tendsto (fun n => eLpNorm (fun x => gn n x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => an n x • gn n x - a x • g x) 2 μ)
      atTop (𝓝 0) := by
  have hfirst : Tendsto (fun n => eLpNorm (fun x => an n x • (gn n x - g x)) 2 μ)
      atTop (𝓝 0) := by
    have hu : Tendsto (fun n => ENNReal.ofReal C *
        eLpNorm (fun x => gn n x - g x) 2 μ) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul
        (a := ENNReal.ofReal C) hglim (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun _ => zero_le _)
    intro n
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul _ 2
    filter_upwards [hbn n] with x hx
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hsecond := tendsto_eLpNorm_bounded_coeff_smul han ha hg hbn hba halim
  have hsum : Tendsto (fun n =>
      eLpNorm (fun x => an n x • (gn n x - g x)) 2 μ +
      eLpNorm (fun x => (an n x - a x) • g x) 2 μ) atTop (𝓝 0) := by
    simpa only [zero_add] using hfirst.add hsecond
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _)
  intro n
  have heq : (fun x => an n x • gn n x - a x • g x) =
      (fun x => an n x • (gn n x - g x)) + (fun x => (an n x - a x) • g x) := by
    funext x
    simp only [Pi.add_apply, smul_sub, sub_smul]
    abel
  change eLpNorm (fun x => an n x • gn n x - a x • g x) 2 μ ≤ _
  rw [heq]
  exact eLpNorm_add_le ((han n).smul ((hgn n).1.sub hg.1))
    (((han n).sub ha).smul hg.1) (by norm_num)

end Torsion

end

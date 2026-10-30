module

public import Torsion.ShapeChangeOfVariables
public import Torsion.SobolevCore
public import Torsion.ShapeGradient

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Transport of the actual closed H¹₀ graph under smooth domain changes

The weak gradient is transported by the adjoint of the actual differential.
Compact smooth tests are transported by the actual homeomorphism. Finite
measure domination and a bounded differential pass both L² approximations
to the limit, proving membership in the original concrete graph closure.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Shape

theorem gradientPullback_memLp (e : Plane ≃ₜ Plane)
    (he : ContDiff ℝ ∞ (e : Plane → Plane)) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hmap : Measure.map e volume ≤ C • (volume : Measure Plane))
    {B : ℝ} (hB : ∀ z, ‖fderiv ℝ (e : Plane → Plane) z‖ ≤ B)
    {g : Plane → Plane} {p : ℝ≥0∞} (hg : MemLp g p volume) :
    MemLp (gradientPullback e g) p volume := by
  have hgc := memLp_pullback_of_measure_bound e hC hmap hg
  have hd : Continuous (fun z => ContinuousLinearMap.adjoint (fderiv ℝ (e : Plane → Plane) z)) :=
    ContinuousLinearMap.adjoint.continuous.comp (he.continuous_fderiv (by simp))
  have hm : AEStronglyMeasurable (gradientPullback e g) volume :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hd.aestronglyMeasurable.prodMk hgc.aestronglyMeasurable)
  exact hgc.of_le_mul hm (ae_of_all _ (fun z => (gradientPullback_norm_le e g z).trans
    (mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _))))

/-- Composition by a map of finite volume distortion preserves L²
convergence of actual representatives. -/
theorem tendsto_eLpNorm_pullback_zero (e : Plane ≃ₜ Plane)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hmap : Measure.map e volume ≤ C • (volume : Measure Plane))
    {E : Type*} [NormedAddCommGroup E] {F : ℕ → Plane → E}
    (hF : ∀ n, MemLp (F n) 2 volume)
    (hlim : Tendsto (fun n => eLpNorm (F n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n ∘ e) 2 volume) atTop (𝓝 0) := by
  have hb (n : ℕ) := eLpNorm_pullback_le_of_measure_bound e hC hmap
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (hF n)
  have hc : C ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hC
  have ht : Tendsto (fun n => C ^ (1 / (2 : ℝ≥0∞)).toReal *
      eLpNorm (F n) 2 volume) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr hc)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le _) hb

/-- The concrete zero-boundary H¹ graph pulls back under an actual smooth
homeomorphism with finite volume distortion and bounded differential.
This is proved directly from its compact smooth approximation definition. -/
theorem MemH10_pullback {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (e : Plane ≃ₜ Plane) (he : ContDiff ℝ ∞ (e : Plane → Plane))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hmap : Measure.map e volume ≤ C • (volume : Measure Plane))
    {B : ℝ} (hB : ∀ z, ‖fderiv ℝ (e : Plane → Plane) z‖ ≤ B)
    (hu : MemH10 (e '' D) u g) :
    MemH10 D (u ∘ e) (gradientPullback e g) := by
  obtain ⟨hmu, hmg, f, hf, hval, hgrad⟩ := hu
  refine ⟨memLp_pullback_of_measure_bound e hC hmap hmu,
    gradientPullback_memLp e he hC hmap hB hmg,
    (fun n => f n ∘ e), (fun n => test_pullback e he (hf n)), ?_, ?_⟩
  · have hv := tendsto_eLpNorm_pullback_zero e hC hmap
      (F := fun n z => f n z - u z) (fun n => (hf n).memLp_value.sub hmu) hval
    simpa only [Function.comp_apply] using hv
  · let H : ℕ → Plane → Plane := fun n z => gradient (f n) z - g z
    have hH (n : ℕ) : MemLp (H n) 2 volume := (hf n).memLp_gradient.sub hmg
    have hl : Tendsto (fun n => eLpNorm (H n ∘ e) 2 volume) atTop (𝓝 0) :=
      tendsto_eLpNorm_pullback_zero e hC hmap hH hgrad
    have hcoeff : Tendsto (fun n => ENNReal.ofReal B *
        eLpNorm (H n ∘ e) 2 volume) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hl (Or.inr ENNReal.ofReal_ne_top)
    have hb (n : ℕ) : eLpNorm (fun z => gradient (f n ∘ e) z - gradientPullback e g z)
        2 volume ≤ ENNReal.ofReal B * eLpNorm (H n ∘ e) 2 volume := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul _ 2
      filter_upwards [] with z
      rw [gradient_comp ((he.differentiable (by simp)) z)
        (((hf n).1.differentiable (by simp)) (e z))]
      have heq : gradientPullback e (gradient (f n)) z - gradientPullback e g z =
          gradientPullback e (H n) z := by
        simp only [gradientPullback, H, map_sub]
      rw [heq]
      exact (gradientPullback_norm_le e (H n) z).trans
        (mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcoeff
      (fun _ => zero_le _) hb

end Torsion.Shape

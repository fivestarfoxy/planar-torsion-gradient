module

public import Torsion.Proof.PaperHermiteHadamard
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! # Arclength of the physical boundary parametrization -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace Torsion.HermiteHadamard

/-- Arclength with multiplicity, the pushforward of speed times Lebesgue
measure on the parameter interval. -/
def curveArclength (γ : ℝ → Plane) (a b : ℝ) : Measure Plane :=
  Measure.map γ ((volume.restrict (Icc a b)).withDensity (fun t => ENNReal.ofReal ‖deriv γ t‖))

theorem curveArclength_finite {γ : ℝ → Plane} (hγ : ContDiff ℝ 1 γ) (a b : ℝ) :
    IsFiniteMeasure (curveArclength γ a b) := by
  have hs := (hγ.continuous_deriv (by norm_num)).norm
  have hI := hs.continuousOn.integrableOn_compact (μ := volume) (isCompact_Icc (a := a) (b := b))
  have := isFiniteMeasure_withDensity (μ := volume.restrict (Icc a b))
    ((lintegral_ofReal_ne_top_iff_integrable hs.aestronglyMeasurable.restrict
      (ae_of_all _ fun _ => norm_nonneg _)).mpr hI)
  unfold curveArclength
  infer_instance

/-- The arclength measure is carried by any measurable set containing the
parametrized arc. -/
theorem curveArclength_ae_mem {γ : ℝ → Plane} (hγ : Continuous γ) {a b : ℝ}
    {K : Set Plane} (hK : MeasurableSet K) (htrace : MapsTo γ (Icc a b) K) :
    ∀ᵐ z ∂curveArclength γ a b, z ∈ K := by
  unfold curveArclength
  apply (ae_map_iff hγ.aemeasurable hK).mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  exact (ae_restrict_mem measurableSet_Icc).mono fun t ht => htrace ht

/-- Integration against geometric arclength equals the ordinary speed-weighted
parameter integral. -/
theorem integral_curveArclength {γ : ℝ → Plane} (hγ : ContDiff ℝ 1 γ) (a b : ℝ)
    {f : Plane → ℝ} (hf : Measurable f) :
    (∫ z, f z ∂curveArclength γ a b) = ∫ t in Icc a b, ‖deriv γ t‖ * f (γ t) := by
  unfold curveArclength
  rw [integral_map hγ.continuous.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul]
  · exact (hγ.continuous_deriv (by norm_num)).norm.measurable.ennreal_ofReal
  · exact ae_of_all _ fun t => ENNReal.ofReal_lt_top

/-- Restricting the arclength integral to any measurable carrier containing the
parametrized arc preserves the ordinary speed-weighted integral. -/
theorem setIntegral_curveArclength {γ : ℝ → Plane} (hγ : ContDiff ℝ 1 γ) {a b : ℝ}
    {K : Set Plane} (hK : MeasurableSet K) (htrace : MapsTo γ (Icc a b) K)
    {f : Plane → ℝ} (hf : Measurable f) :
    (∫ z in K, f z ∂curveArclength γ a b) = ∫ t in Icc a b, f (γ t) * ‖deriv γ t‖ := by
  rw [← integral_indicator hK, integral_curveArclength hγ _ _ (hf.indicator hK)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [indicator_of_mem (htrace hx), mul_comm]

/-- Every ball about every point of a regular compact parametrized arc has
positive arclength, including the two endpoint parameters. -/
theorem curveArclength_mass_ball {γ : ℝ → Plane} (hγ : ContDiff ℝ 1 γ) {a b : ℝ} (hab : a < b)
    (hreg : ∀ t ∈ Icc a b, deriv γ t ≠ 0) {K : Set Plane} (hK : MeasurableSet K)
    (htrace : MapsTo γ (Icc a b) K) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ} (hr : 0 < r) :
    0 < ((curveArclength γ a b).restrict K) (Metric.ball (γ t) r) := by
  let B := Metric.ball (γ t) r
  let A := γ ⁻¹' B
  have hA : IsOpen A := Metric.isOpen_ball.preimage hγ.continuous
  have htA : t ∈ A := Metric.mem_ball_self hr
  have hcl : t ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
  have hne : (A ∩ Ioo a b).Nonempty := mem_closure_iff_nhds.mp hcl _ (hA.mem_nhds htA)
  have hv : 0 < volume (A ∩ Ioo a b) := (hA.inter isOpen_Ioo).measure_pos volume hne
  let μ := volume.restrict (Icc a b)
  let d := fun x => ENNReal.ofReal ‖deriv γ x‖
  have hd : Measurable d := (hγ.continuous_deriv (by norm_num)).norm.measurable.ennreal_ofReal
  have hdpos : ∀ᵐ x ∂μ, d x ≠ 0 := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Icc a b) measurableSet_Icc] with x hx
    exact (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (hreg x hx))).ne'
  have hμ : 0 < μ (γ ⁻¹' (B ∩ K)) := by
    change 0 < volume.restrict (Icc a b) _
    rw [Measure.restrict_apply (hγ.continuous.measurable (Metric.isOpen_ball.measurableSet.inter hK))]
    apply hv.trans_le (measure_mono _)
    intro x hx
    have hxi := Ioo_subset_Icc_self hx.2
    exact ⟨⟨hx.1, htrace hxi⟩, hxi⟩
  rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet, curveArclength,
    Measure.map_apply hγ.continuous.measurable (Metric.isOpen_ball.measurableSet.inter hK)]
  exact pos_iff_ne_zero.mpr (fun h => hμ.ne' (withDensity_absolutelyContinuous' hd.aemeasurable hdpos h))

end Torsion.HermiteHadamard

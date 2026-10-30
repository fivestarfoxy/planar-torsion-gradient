import Torsion.RestrictedSpectralRegularRepresentative
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Quadratic vanishing at an analytic nonnegative zero

Twice taking the genuine analytic divided slope factors a local analytic
minimum as (x-x₀)² times a continuous function. The resulting actual
quadratic bound removes the apparent double-pole singularity in the
real-space half-Laplacian kernel.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- An analytic nonnegative zero has an actual quadratic bound on a
neighborhood. The two divided slopes provide the factor directly. -/
theorem exists_quadratic_bound_of_analytic_nonneg_zero {f : ℝ → ℝ} {x₀ : ℝ}
    (hf : AnalyticAt ℝ f x₀) (hnonneg : ∀ᶠ s : ℝ in 𝓝 x₀, 0 ≤ f s)
    (hzero : f x₀ = 0) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ s ∈ Metric.ball x₀ δ, |f s| ≤ K * (s - x₀) ^ 2 := by
  have hmin : IsLocalMin f x₀ := by
    change ∀ᶠ s : ℝ in 𝓝 x₀, f x₀ ≤ f s
    simpa only [hzero] using hnonneg
  have hd : deriv f x₀ = 0 := hmin.deriv_eq_zero
  obtain ⟨p, hp⟩ := hf
  let q : ℝ → ℝ := dslope (dslope f x₀) x₀
  have hq : ContinuousAt q x₀ :=
    hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope.continuousAt
  have hbound : ∀ᶠ s : ℝ in 𝓝 x₀, |q s| < |q x₀| + 1 :=
    hq.abs.tendsto.eventually (Iio_mem_nhds (lt_add_one _))
  obtain ⟨δ, hδ, hδbound⟩ := Metric.mem_nhds_iff.1 hbound
  refine ⟨δ, |q x₀| + 1, hδ, by positivity, ?_⟩
  intro s hs
  have hfactor : (s - x₀) ^ 2 * q s = f s := by
    have h1 := sub_smul_dslope f x₀ s
    have h2 := sub_smul_dslope (dslope f x₀) x₀ s
    simp only [smul_eq_mul, dslope_same, hd, hzero, sub_zero] at h1 h2
    dsimp only [q]
    calc
      (s - x₀) ^ 2 * dslope (dslope f x₀) x₀ s =
          (s - x₀) * ((s - x₀) * dslope (dslope f x₀) x₀ s) := by ring
      _ = (s - x₀) * dslope f x₀ s := congrArg (fun z => (s - x₀) * z) h2
      _ = f s := h1
  rw [← hfactor, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (hδbound hs).le (sq_nonneg _)).trans_eq (by ring)


/-- A global L¹ function with genuine local quadratic vanishing has an
integrable double-pole quotient. The quotient is bounded near the zero,
and is dominated by a fixed multiple of the original L¹ datum outside. -/
theorem integrable_div_sq_of_quadratic_bound {f : ℝ → ℝ} {x₀ δ K : ℝ}
    (hf : Integrable f) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hquad : ∀ s ∈ Metric.ball x₀ δ, |f s| ≤ K * (s - x₀) ^ 2) :
    Integrable (fun s : ℝ => f s / (x₀ - s) ^ 2) := by
  let g : ℝ → ℝ := fun s => f s / (x₀ - s) ^ 2
  have hgm : AEStronglyMeasurable g volume :=
    (hf.aestronglyMeasurable.aemeasurable.div
      ((continuous_const.sub continuous_id).pow 2).aemeasurable).aestronglyMeasurable
  have hnorm (s : ℝ) : ‖g s‖ = |f s| / (x₀ - s) ^ 2 := by
    simp only [g, Real.norm_eq_abs, abs_div, abs_pow, sq_abs]
  have hfinite : volume (Metric.ball x₀ δ) < (⊤ : ℝ≥0∞) :=
    (measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall x₀ δ).measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ δ)) := ⟨by simp [hfinite]⟩
  have hnear : IntegrableOn g (Metric.ball x₀ δ) := by
    apply (integrable_const K).mono' hgm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball] with s hs
    rw [hnorm]
    by_cases hzero : x₀ = s
    · simp only [hzero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, div_zero]
      exact hK
    · have hden : 0 < (x₀ - s) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.2 hzero)
      apply (div_le_iff₀ hden).2
      simpa only [show (s - x₀) ^ 2 = (x₀ - s) ^ 2 from by ring] using hquad s hs
  have hfar : IntegrableOn g (Metric.ball x₀ δ)ᶜ := by
    apply ((hf.norm.const_mul ((δ ^ 2)⁻¹)).integrableOn).mono' hgm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with s hs
    have hdist : δ ≤ |x₀ - s| := by
      have h : δ ≤ dist s x₀ := le_of_not_gt hs
      simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using h
    have hsq : δ ^ 2 ≤ (x₀ - s) ^ 2 := by nlinarith [sq_abs (x₀ - s)]
    rw [hnorm, Real.norm_eq_abs]
    calc
      |f s| / (x₀ - s) ^ 2 ≤ |f s| / δ ^ 2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hδ) hsq
      _ = (δ ^ 2)⁻¹ * |f s| := by ring
  have hall := hnear.union hfar
  simpa only [union_compl_self, integrableOn_univ] using hall

/-- The absolute-value version of the double-pole quotient is genuinely
integrable under the same concrete local quadratic bound. -/
theorem integrable_abs_div_sq_of_quadratic_bound {f : ℝ → ℝ} {x₀ δ K : ℝ}
    (hf : Integrable f) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hquad : ∀ s ∈ Metric.ball x₀ δ, |f s| ≤ K * (s - x₀) ^ 2) :
    Integrable (fun s : ℝ => |f s| / (x₀ - s) ^ 2) := by
  have h := (integrable_div_sq_of_quadratic_bound hf hδ hK hquad).norm
  simpa only [Real.norm_eq_abs, abs_div, abs_pow, sq_abs] using h

/-- The singular quotient is integrable at every nonnegative analytic
zero of a genuine global L¹ function. -/
theorem integrable_div_sq_of_analytic_nonneg_zero {f : ℝ → ℝ} {x₀ : ℝ}
    (hf : Integrable f) (ha : AnalyticAt ℝ f x₀)
    (hnonneg : ∀ᶠ s : ℝ in 𝓝 x₀, 0 ≤ f s) (hzero : f x₀ = 0) :
    Integrable (fun s : ℝ => f s / (x₀ - s) ^ 2) := by
  obtain ⟨δ, K, hδ, hK, hquad⟩ := exists_quadratic_bound_of_analytic_nonneg_zero ha hnonneg hzero
  exact integrable_div_sq_of_quadratic_bound hf hδ hK.le hquad


/-- At a hypothetical interior zero, the actual analytic representative
of the original nonnegative-half eigenfunction vanishes quadratically. -/
theorem IsRestrictedEigenfunction.regularEigenfunction_quadratic_bound
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) (hzero : regularEigenfunction f x₀ = 0) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ s ∈ Metric.ball x₀ δ, |regularEigenfunction f s| ≤ K * (s - x₀) ^ 2 := by
  apply exists_quadratic_bound_of_analytic_nonneg_zero
    (hf.regularEigenfunction_analyticAt hodd x₀ ⟨by linarith [hx₀.1], hx₀.2⟩) ?_ hzero
  filter_upwards [isOpen_Ioo.mem_nhds hx₀] with s hs
  exact hf.regularEigenfunction_nonneg hodd hnonneg s hs

/-- The actual double-pole quotient of the genuine analytic spectral
representative is integrable at a hypothetical nonnegative interior zero. -/
theorem IsRestrictedEigenfunction.regularEigenfunction_div_sq_integrable
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) (hzero : regularEigenfunction f x₀ = 0) :
    Integrable (fun s : ℝ => regularEigenfunction f s / (x₀ - s) ^ 2) := by
  obtain ⟨δ, K, hδ, hK, hquad⟩ := hf.regularEigenfunction_quadratic_bound hodd hnonneg hx₀ hzero
  exact integrable_div_sq_of_quadratic_bound
    (hf.regularEigenfunction_isRestrictedEigenfunction hodd).1.integrable hδ hK.le hquad


/-- The integrability statement also holds for the original arbitrary
L² representative, since the actual functions agree almost everywhere. -/
theorem IsRestrictedEigenfunction.div_sq_integrable_of_regularEigenfunction_zero
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) (hzero : regularEigenfunction f x₀ = 0) :
    Integrable (fun s : ℝ => f s / (x₀ - s) ^ 2) := by
  apply (hf.regularEigenfunction_div_sq_integrable hodd hnonneg hx₀ hzero).congr
  filter_upwards [hf.regularEigenfunction_ae_eq hodd] with s hs
  rw [hs]

end Torsion.Spectral

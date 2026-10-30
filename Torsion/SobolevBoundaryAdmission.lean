module

public import Torsion.SmoothPositivePart
public import Torsion.SobolevComposition
public import Torsion.L2Dominated
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Data.Complex.FiniteDimensional
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Direct H¹₀ admission from positive smooth zero-boundary data

Shifted flat scalar truncations have compact positive level support. Their
actual smooth gradients converge by dominated convergence. The construction
does not assume a Lipschitz boundary or a trace-characterization theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.BoundaryAdmission

def threshold (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem threshold_pos (n : ℕ) : 0 < threshold n := by
  unfold threshold
  positivity

theorem threshold_tendsto : Tendsto threshold atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def truncation (n : ℕ) (t : ℝ) : ℝ :=
  SmoothPositivePart.approx n (t - threshold n)

def coefficient (n : ℕ) (t : ℝ) : ℝ :=
  SmoothPositivePart.slope n (t - threshold n)

theorem truncation_zero_of_le (n : ℕ) {t : ℝ} (ht : t ≤ threshold n) :
    truncation n t = 0 :=
  SmoothPositivePart.approx_zero_of_nonpos n (sub_nonpos.mpr ht)

theorem truncation_contDiff (n : ℕ) : ContDiff ℝ ∞ (truncation n) :=
  (SmoothPositivePart.approx_contDiff n).comp (contDiff_id.sub contDiff_const)

theorem truncation_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (truncation n) (coefficient n t) t := by
  simpa only [truncation, coefficient, mul_one] using
    (SmoothPositivePart.approx_hasDerivAt n (t - threshold n)).comp t
      ((hasDerivAt_id t).sub_const (threshold n))

theorem coefficient_norm_le_one (n : ℕ) (t : ℝ) : ‖coefficient n t‖ ≤ 1 :=
  SmoothPositivePart.slope_norm_le_one n _

theorem truncation_norm_le {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ‖truncation n t‖ ≤ t := by
  by_cases hsmall : t ≤ threshold n
  · rw [truncation_zero_of_le n hsmall, norm_zero]
    exact ht
  · have hpos : 0 < t - threshold n := sub_pos.mpr (lt_of_not_ge hsmall)
    exact (SmoothPositivePart.approx_norm_le n _).trans
      (by rw [Real.norm_eq_abs, abs_of_pos hpos]; linarith [threshold_pos n])

theorem truncation_tendsto {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => truncation n t) atTop (𝓝 t) := by
  have hbase : Tendsto (fun n => SmoothPositivePart.approx n t) atTop (𝓝 t) := by
    simpa only [max_eq_left ht] using SmoothPositivePart.tendsto_approx t
  apply hbase.congr_dist
  apply squeeze_zero (fun _ => dist_nonneg) _ threshold_tendsto
  intro n
  have h := (SmoothPositivePart.approx_lipschitz n).dist_le_mul t (t - threshold n)
  simpa only [truncation, NNReal.coe_one, one_mul, Real.dist_eq,
    sub_sub_cancel, abs_of_pos (threshold_pos n)] using h

theorem coefficient_tendsto_one {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => coefficient n t) atTop (𝓝 1) := by
  have hevent : (fun n => coefficient n t) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / t)
    filter_upwards [eventually_ge_atTop N] with n hn
    apply Real.smoothTransition.one_of_one_le
    have hnr : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnt : 2 < (N : ℝ) * t := (div_lt_iff₀ ht).mp hN
    have hden : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    change 1 ≤ ((n : ℝ) + 1) * (t - 1 / ((n : ℝ) + 1))
    rw [mul_sub, mul_one_div_cancel hden]
    nlinarith
  exact (tendsto_congr' hevent).2 tendsto_const_nhds

/-- Each positive level truncation is an actual C∞ compact test inside the
domain. The continuity of the zero extension keeps its support away from
the entire boundary, however irregular that boundary may be. -/
theorem truncation_isTest {D : Set Plane} (hD : IsOpen D) (hb : Bornology.IsBounded D)
    {u : Plane → ℝ} (hc : Continuous u) (hs : ContDiffOn ℝ ∞ u D)
    (hzero : ∀ x ∉ D, u x = 0) (n : ℕ) :
    IsTest D (fun x => truncation n (u x)) := by
  have hlevel : IsClosed {x : Plane | threshold n ≤ u x} :=
    isClosed_le continuous_const hc
  have hsupport : Function.support (fun x => truncation n (u x)) ⊆
      {x : Plane | threshold n ≤ u x} := by
    intro x hx
    by_contra h
    exact hx (truncation_zero_of_le n (le_of_not_ge h))
  have htsupport : tsupport (fun x => truncation n (u x)) ⊆
      {x : Plane | threshold n ≤ u x} := closure_minimal hsupport hlevel
  have htsD : tsupport (fun x => truncation n (u x)) ⊆ D := by
    intro x hx
    by_contra hxD
    have hx' := htsupport hx
    change threshold n ≤ u x at hx'
    rw [hzero x hxD] at hx'
    exact (not_le_of_gt (threshold_pos n)) hx'
  refine ⟨?_, ?_, htsD⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ D
    · exact (truncation_contDiff n).contDiffAt.comp x
        ((hs x hx).contDiffAt (hD.mem_nhds hx))
    · have hu0 : u x = 0 := hzero x hx
      have hevent : ∀ᶠ y in 𝓝 x, u y < threshold n :=
        hc.continuousAt.eventually_lt continuous_const.continuousAt
          (by rw [hu0]; exact threshold_pos n)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hevent] with y hy
      exact truncation_zero_of_le n hy.le
  · exact Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _) (hb.subset htsD)

/-- Direct density theorem for positive smooth interior data with continuous
zero extension and finite actual value/gradient L² norms. -/
theorem memH10_of_positive_zero_extension {D : Set Plane}
    (hD : IsOpen D) (hb : Bornology.IsBounded D)
    {u : Plane → ℝ} {g : Plane → Plane}
    (hc : Continuous u) (hs : ContDiffOn ℝ ∞ u D)
    (hpos : ∀ x ∈ D, 0 < u x) (hzero : ∀ x ∉ D, u x = 0)
    (hgrad : ∀ x ∈ D, g x = gradient u x) (hgzero : ∀ x ∉ D, g x = 0)
    (huLp : MemLp u 2 volume) (hgLp : MemLp g 2 volume) : MemH10 D u g := by
  have hu0 : ∀ x, 0 ≤ u x := by
    intro x
    by_cases hx : x ∈ D
    · exact (hpos x hx).le
    · rw [hzero x hx]
  let f : ℕ → Plane → ℝ := fun n x => truncation n (u x)
  have hf : ∀ n, IsTest D (f n) :=
    fun n => truncation_isTest hD hb hc hs hzero n
  have hfg : ∀ n x, gradient (f n) x = coefficient n (u x) • g x := by
    intro n x
    by_cases hx : x ∈ D
    · have hdiff : DifferentiableAt ℝ u x :=
        ((hs x hx).contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
      have hd := (truncation_hasDerivAt n (u x)).comp_hasFDerivAt x
        hdiff.hasGradientAt.hasFDerivAt
      have hg : HasGradientAt (f n) (coefficient n (u x) • gradient u x) x := by
        apply hasGradientAt_iff_hasFDerivAt.mpr
        simpa only [map_smul, RCLike.conj_to_real] using hd
      rw [hg.gradient, hgrad x hx]
    · have hnot : x ∉ tsupport (f n) := fun h => hx ((hf n).2.2 h)
      rw [gradient_eq_zero_of_not_mem_tsupport hnot, hgzero x hx, smul_zero]
  refine ⟨huLp, hgLp, f, hf, ?_, ?_⟩
  · apply tendsto_eLpNorm_two_of_dominated (B := fun x => 2 * ‖u x‖)
    · intro n
      exact ((hf n).1.continuous.aestronglyMeasurable.sub huLp.1)
    · convert ((memLp_two_iff_integrable_sq_norm huLp.1).mp huLp).const_mul (4 : ℝ) using 1
      funext x
      ring
    · intro n
      exact ae_of_all _ fun x => (norm_sub_le _ _).trans (by
        have hn := truncation_norm_le (hu0 x) n
        have huabs : ‖u x‖ = u x := Real.norm_of_nonneg (hu0 x)
        change ‖truncation n (u x)‖ + ‖u x‖ ≤ 2 * ‖u x‖
        rw [huabs]
        linarith)
    · exact ae_of_all _ fun x => by
        simpa only [sub_self] using (truncation_tendsto (hu0 x)).sub_const (u x)
  · apply tendsto_eLpNorm_two_of_dominated (B := fun x => 2 * ‖g x‖)
    · intro n
      exact (hf n).continuous_gradient.aestronglyMeasurable.sub hgLp.1
    · convert ((memLp_two_iff_integrable_sq_norm hgLp.1).mp hgLp).const_mul (4 : ℝ) using 1
      funext x
      ring
    · intro n
      exact ae_of_all _ fun x => (norm_sub_le _ _).trans (by
        rw [hfg, norm_smul]
        have hn := coefficient_norm_le_one n (u x)
        nlinarith [norm_nonneg (g x)])
    · exact ae_of_all _ fun x => by
        simp only [hfg]
        by_cases hx : x ∈ D
        · simpa only [one_smul, sub_self] using
            ((coefficient_tendsto_one (hpos x hx)).smul_const (g x)).sub_const (g x)
        · simp only [hgzero x hx, smul_zero, sub_zero]
          exact tendsto_const_nhds

end Torsion.BoundaryAdmission

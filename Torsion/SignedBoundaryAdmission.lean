module

public import Torsion.SmoothZeroLevel
public import Torsion.SobolevBoundaryAdmission

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Signed zero-boundary admission in the original Sobolev graph

Flat positive-level truncations admit both signs. The local zero-level
gradient theorem identifies the gradient of their difference. The domain
need not have a Lipschitz boundary.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.BoundaryAdmission

theorem truncation_norm_le_abs (n : ℕ) (t : ℝ) : ‖truncation n t‖ ≤ ‖t‖ := by
  by_cases ht : 0 ≤ t
  · simpa [Real.norm_of_nonneg ht] using truncation_norm_le ht n
  · rw [truncation_zero_of_le n ((le_of_not_ge ht).trans (threshold_pos n).le), norm_zero]
    exact norm_nonneg _

theorem truncation_tendsto_pos_part (t : ℝ) :
    Tendsto (fun n => truncation n t) atTop (𝓝 (max t 0)) := by
  by_cases ht : 0 ≤ t
  · simpa [max_eq_left ht] using truncation_tendsto ht
  · have hn : t ≤ 0 := le_of_not_ge ht
    simpa only [truncation_zero_of_le _ (hn.trans (threshold_pos _).le),
      max_eq_right hn] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem coefficient_tendsto_pos_indicator (t : ℝ) :
    Tendsto (fun n => coefficient n t) atTop (𝓝 (if 0 < t then (1 : ℝ) else 0)) := by
  by_cases ht : 0 < t
  · simpa [ht] using coefficient_tendsto_one ht
  · have hz (n : ℕ) : coefficient n t = 0 :=
      SmoothPositivePart.slope_zero_of_nonpos n (by linarith [threshold_pos n])
    simpa only [hz, if_neg ht] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- The positive part of signed smooth zero-boundary data has its genuine
positive-part weak gradient in the original graph closure. -/
theorem memH10_pos_part_of_zero_extension {D : Set Plane}
    (hD : IsOpen D) (hb : Bornology.IsBounded D)
    {u : Plane → ℝ} {g : Plane → Plane}
    (hc : Continuous u) (hs : ContDiffOn ℝ ∞ u D)
    (hzero : ∀ x ∉ D, u x = 0)
    (hgrad : ∀ x ∈ D, g x = gradient u x) (hgzero : ∀ x ∉ D, g x = 0)
    (huLp : MemLp u 2 volume) (hgLp : MemLp g 2 volume) :
    MemH10 D (fun x => max (u x) 0) (fun x => if 0 < u x then g x else 0) := by
  let k : Plane → Plane := fun x => if 0 < u x then g x else 0
  have hk : MemLp k 2 volume := by
    simpa only [k, indicator_apply, mem_setOf_eq] using
      hgLp.indicator (isOpen_lt continuous_const hc).measurableSet
  let f : ℕ → Plane → ℝ := fun n x => truncation n (u x)
  have hf (n : ℕ) : IsTest D (f n) := truncation_isTest hD hb hc hs hzero n
  have hfg (n : ℕ) (x : Plane) :
      gradient (f n) x = coefficient n (u x) • g x := by
    by_cases hx : x ∈ D
    · have hdiff : DifferentiableAt ℝ u x :=
        ((hs x hx).contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
      have hd := (truncation_hasDerivAt n (u x)).comp_hasFDerivAt x
        hdiff.hasGradientAt.hasFDerivAt
      have hG : HasGradientAt (f n) (coefficient n (u x) • gradient u x) x := by
        apply hasGradientAt_iff_hasFDerivAt.mpr
        simpa only [map_smul, RCLike.conj_to_real] using hd
      rw [hG.gradient, hgrad x hx]
    · rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hx ((hf n).2.2 h)),
        hgzero x hx, smul_zero]
  refine ⟨huLp.pos_part, hk, f, hf, ?_, ?_⟩
  · apply tendsto_eLpNorm_two_of_dominated (B := fun x => 2 * ‖u x‖)
    · intro n
      exact (hf n).1.continuous.aestronglyMeasurable.sub huLp.pos_part.1
    · convert ((memLp_two_iff_integrable_sq_norm huLp.1).mp huLp).const_mul (4 : ℝ) using 1
      funext x
      ring
    · intro n
      exact ae_of_all _ fun x => (norm_sub_le _ _).trans (by
        have hmax : ‖max (u x) 0‖ ≤ ‖u x‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
          exact max_le (le_abs_self _) (abs_nonneg _)
        linarith [truncation_norm_le_abs n (u x)])
    · exact ae_of_all _ fun x => by
        simpa only [sub_self] using (truncation_tendsto_pos_part (u x)).sub_const (max (u x) 0)
  · apply tendsto_eLpNorm_two_of_dominated (B := fun x => 2 * ‖g x‖)
    · intro n
      exact (hf n).continuous_gradient.aestronglyMeasurable.sub hk.1
    · convert ((memLp_two_iff_integrable_sq_norm hgLp.1).mp hgLp).const_mul (4 : ℝ) using 1
      funext x
      ring
    · intro n
      exact ae_of_all _ fun x => (norm_sub_le _ _).trans (by
        rw [hfg, norm_smul]
        have hkn : ‖k x‖ ≤ ‖g x‖ := by
          dsimp [k]
          split_ifs <;> simp
        have hn := coefficient_norm_le_one n (u x)
        nlinarith [norm_nonneg (g x)])
    · exact ae_of_all _ fun x => by
        have hlim := ((coefficient_tendsto_pos_indicator (u x)).smul_const (g x)).sub_const (k x)
        have heq : (if 0 < u x then (1 : ℝ) else 0) • g x = k x := by
          dsimp [k]
          split_ifs <;> simp
        simpa only [hfg, heq, sub_self] using hlim

/-- A continuous zero extension, smooth interior, and finite actual L²
value/gradient norms suffice for signed H¹₀ admission. Positivity and
boundary regularity are unnecessary. -/
theorem memH10_of_smooth_zero_extension {D : Set Plane}
    (hD : IsOpen D) (hb : Bornology.IsBounded D)
    {u : Plane → ℝ} {g : Plane → Plane}
    (hc : Continuous u) (hs : ContDiffOn ℝ ∞ u D)
    (hzero : ∀ x ∉ D, u x = 0)
    (hgrad : ∀ x ∈ D, g x = gradient u x) (hgzero : ∀ x ∉ D, g x = 0)
    (huLp : MemLp u 2 volume) (hgLp : MemLp g 2 volume) : MemH10 D u g := by
  have hp := memH10_pos_part_of_zero_extension hD hb hc hs hzero hgrad hgzero huLp hgLp
  have hn := memH10_pos_part_of_zero_extension hD hb hc.neg hs.neg
    (fun x hx => by simp [hzero x hx])
    (fun x hx => by
      have hd := ((hs x hx).contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
      change -(g x) = gradient (fun x => -u x) x
      rw [hgrad x hx]
      unfold gradient
      rw [fderiv_neg, map_neg])
    (fun x hx => by simp [hgzero x hx]) huLp.neg hgLp.neg
  have hzeroAE : ∀ᵐ x ∂volume, u x = 0 → g x = 0 := by
    have hz := (ae_restrict_iff' hD.measurableSet).mp
      (Torsion.ContDiffOn.gradient_ae_zero_on_zero hD hs)
    filter_upwards [hz] with x hx hu0
    by_cases hxD : x ∈ D
    · rw [hgrad x hxD]
      exact hx hxD hu0
    · exact hgzero x hxD
  apply (hp.sub hn).congr
  · exact ae_of_all _ fun x => max_zero_sub_max_neg_zero_eq_self (u x)
  · filter_upwards [hzeroAE] with x hx
    by_cases hp : 0 < u x
    · simp [hp, not_lt.mpr (neg_nonpos.mpr hp.le)]
    · by_cases hn : 0 < -u x
      · simp [hp, hn]
      · have hu0 : u x = 0 := by linarith
        simp [hp, hn, hx hu0]

end Torsion.BoundaryAdmission

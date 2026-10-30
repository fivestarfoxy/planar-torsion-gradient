module

public import Torsion.SobolevLattice
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Strong H¹ continuity of the positive part -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace Torsion

/-- Cutting an a.e.-measurable field to a measurable value superlevel
preserves a.e. strong measurability, without choosing special representatives. -/
theorem aestronglyMeasurable_positive_cut
    {u : Plane → ℝ} {g : Plane → Plane}
    (hu : AEStronglyMeasurable u volume) (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun x => if 0 < u x then g x else 0) volume := by
  refine ⟨fun x => if 0 < hu.mk u x then hg.mk g x else 0, ?_, ?_⟩
  · exact StronglyMeasurable.ite
      (measurableSet_lt measurable_const hu.stronglyMeasurable_mk.measurable)
      hg.stronglyMeasurable_mk stronglyMeasurable_const
  · filter_upwards [hu.ae_eq_mk, hg.ae_eq_mk] with x hx hy
    simp only [hx, hy]

private theorem positive_cut_tendsto_at_zero_level
    {a : ℕ → ℝ} {t : ℝ} {g : Plane}
    (ha : Tendsto a atTop (𝓝 t)) (hg : t = 0 → g = 0) :
    Tendsto (fun n => (if 0 < a n then g else 0) - (if 0 < t then g else 0))
      atTop (𝓝 0) := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · apply tendsto_const_nhds.congr'
    filter_upwards [ha.eventually (gt_mem_nhds ht)] with n hn
    simp [not_lt.mpr hn.le, not_lt.mpr ht.le]
  · have hz := hg ht
    simp only [hz, ite_self, sub_self]
    exact tendsto_const_nhds
  · apply tendsto_const_nhds.congr'
    filter_upwards [ha.eventually (lt_mem_nhds ht)] with n hn
    simp [hn, ht]

/-- L² continuity of superlevel truncation along a.e.-convergent values and
L²-convergent fields, provided the limiting field vanishes on the zero level.
The latter property is proved for actual Sobolev gradients in `SobolevLattice`. -/
theorem tendsto_eLpNorm_positive_cut_of_ae
    {uₙ : ℕ → Plane → ℝ} {u : Plane → ℝ}
    {gₙ : ℕ → Plane → Plane} {g : Plane → Plane}
    (hun : ∀ n, AEStronglyMeasurable (uₙ n) volume)
    (hu : AEStronglyMeasurable u volume)
    (hgn : ∀ n, MemLp (gₙ n) 2 volume) (hg : MemLp g 2 volume)
    (hvalue : ∀ᵐ x ∂volume, Tendsto (fun n => uₙ n x) atTop (𝓝 (u x)))
    (hlevel : ∀ᵐ x ∂volume, u x = 0 → g x = 0)
    (hgrad : Tendsto (fun n => eLpNorm (fun x => gₙ n x - g x) 2 volume)
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x =>
      (if 0 < uₙ n x then gₙ n x else 0) - (if 0 < u x then g x else 0)) 2 volume)
      atTop (𝓝 0) := by
  have hfirst : Tendsto (fun n => eLpNorm
      (fun x => if 0 < uₙ n x then gₙ n x - g x else 0) 2 volume) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgrad
      (fun _ => zero_le)
    intro n
    apply eLpNorm_mono
      (aestronglyMeasurable_positive_cut (hun n) ((hgn n).aestronglyMeasurable.sub hg.aestronglyMeasurable))
    intro x
    split_ifs <;> simp
  have hsecond : Tendsto (fun n => eLpNorm
      (fun x => (if 0 < uₙ n x then g x else 0) - (if 0 < u x then g x else 0))
      2 volume) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_dominated (B := fun x => 2 * ‖g x‖)
    · intro n
      exact (aestronglyMeasurable_positive_cut (hun n) hg.aestronglyMeasurable).sub
        (aestronglyMeasurable_positive_cut hu hg.aestronglyMeasurable)
    · have hsq := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
      simpa only [mul_pow] using hsq.const_mul ((2 : ℝ) ^ 2)
    · intro n
      apply Eventually.of_forall
      intro x
      split_ifs <;> simp only [sub_self, sub_zero, zero_sub, norm_zero, norm_neg]
        <;> linarith [norm_nonneg (g x)]
    · filter_upwards [hvalue, hlevel] with x hx hl
      exact positive_cut_tendsto_at_zero_level hx hl
  have hsum : Tendsto (fun n => eLpNorm
      (fun x => if 0 < uₙ n x then gₙ n x - g x else 0) 2 volume +
      eLpNorm (fun x => (if 0 < uₙ n x then g x else 0) -
        (if 0 < u x then g x else 0)) 2 volume) atTop (𝓝 0) := by
    simpa only [zero_add] using hfirst.add hsecond
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro n
  have heq : (fun x => (if 0 < uₙ n x then gₙ n x else 0) -
        (if 0 < u x then g x else 0)) =
      (fun x => if 0 < uₙ n x then gₙ n x - g x else 0) +
        (fun x => (if 0 < uₙ n x then g x else 0) - (if 0 < u x then g x else 0)) := by
    funext x
    simp only [Pi.add_apply]
    split_ifs <;> abel
  dsimp only
  rw [heq]
  exact eLpNorm_add_le (by norm_num)

/-- The positive part is strongly continuous in the actual H¹ graph.
Every subsequence has an a.e.-convergent further subsequence in the value
coordinate; the proved zero-level property then gives L² gradient convergence. -/
theorem MemH10.tendsto_eLpNorm_pos_part
    {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    {uₙ : ℕ → Plane → ℝ} {gₙ : ℕ → Plane → Plane}
    (hu : MemH10 D u g) (hun : ∀ n, MemH10 D (uₙ n) (gₙ n))
    (hval : Tendsto (fun n => eLpNorm (fun x => uₙ n x - u x) 2 volume) atTop (𝓝 0))
    (hgrad : Tendsto (fun n => eLpNorm (fun x => gₙ n x - g x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Max.max (uₙ n x) 0 - Max.max (u x) 0) 2 volume)
      atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun x => (if 0 < uₙ n x then gₙ n x else 0) -
      (if 0 < u x then g x else 0)) 2 volume) atTop (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · exact tendsto_eLpNorm_lipschitz_comp Lp.lipschitzWith_pos_part
      (fun n => (hun n).1.aestronglyMeasurable) hu.1.aestronglyMeasurable hval
  · apply Filter.tendsto_of_subseq_tendsto
    intro ν hν
    have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm
      (f := fun n => uₙ (ν n)) (g := u) (μ := volume)
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by simpa only [Pi.sub_def, Function.comp_def] using hval.comp hν)
    obtain ⟨κ, hκ, hκae⟩ := hmeasure.exists_seq_tendsto_ae
    refine ⟨κ, ?_⟩
    exact tendsto_eLpNorm_positive_cut_of_ae
      (fun n => (hun (ν (κ n))).1.aestronglyMeasurable) hu.1.aestronglyMeasurable
      (fun n => (hun (ν (κ n))).2.1) hu.2.1 hκae hu.gradient_ae_zero_on_zero
      ((hgrad.comp hν).comp hκ.tendsto_atTop)

end Torsion

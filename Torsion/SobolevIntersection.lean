module

public import Torsion.SobolevIdeal
public import Torsion.SobolevMinContinuity

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Admissible Sobolev tests in an intersection

This proves Lemma 3.2 for the actual graph closure, including arbitrary open
sets with slits. Positive compact approximants of the second upper bound are
minimized with the dominated value. The ideal property first retains the
first zero-trace domain, and compact localization then adds the second one.
Strong H¹ continuity of the lattice operation passes to the original value.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- A nonnegative Sobolev function dominated by zero-boundary functions on two
open domains is an admissible test on their actual intersection. -/
theorem MemH10.of_nonneg_le_inter {D₀ D₁ B : Set Plane}
    {u₀ u₁ v : Plane → ℝ} {g₀ g₁ h : Plane → Plane}
    (hu₀ : MemH10 D₀ u₀ g₀) (hu₁ : MemH10 D₁ u₁ g₁)
    (hv : MemH10 B v h) (hD₀ : IsOpen D₀) (hD₁ : IsOpen D₁)
    (hv0 : ∀ᵐ x ∂volume, 0 ≤ v x)
    (hvu₀ : ∀ᵐ x ∂volume, v x ≤ u₀ x)
    (hvu₁ : ∀ᵐ x ∂volume, v x ≤ u₁ x) :
    MemH10 (D₀ ∩ D₁) v h := by
  classical
  let A := B ∪ (D₀ ∪ D₁)
  have hD₀A : D₀ ⊆ A := fun x hx => Or.inr (Or.inl hx)
  have hD₁A : D₁ ⊆ A := fun x hx => Or.inr (Or.inr hx)
  have hvA : MemH10 A v h := hv.mono subset_union_left
  have hu₁A : MemH10 A u₁ g₁ := hu₁.mono hD₁A
  have hvD₀ : MemH10 D₀ v h := hu₀.of_nonneg_le hv hD₀ hv0 hvu₀
  obtain ⟨_, _, f, hf, hfu, hfg⟩ := hu₁
  have hfA (n : ℕ) : MemH10 A (f n) (gradient (f n)) :=
    (hf n).memH10.mono hD₁A
  let w : ℕ → Plane → ℝ := fun n x => Min.min (v x) (Max.max (f n x) 0)
  let k : ℕ → Plane → Plane := fun n x =>
    if v x ≤ Max.max (f n x) 0 then h x else
      (if 0 < f n x then gradient (f n) x else 0)
  have hwA (n : ℕ) : MemH10 A (w n) (k n) := hvA.min (hfA n).pos_part
  have hwD₀ (n : ℕ) : MemH10 D₀ (w n) (k n) := by
    apply hvD₀.of_nonneg_le (hwA n) hD₀
    · filter_upwards [hv0] with x hx
      exact le_min hx (le_max_right _ _)
    · exact Eventually.of_forall (fun x => min_le_left _ _)
  have hw (n : ℕ) : MemH10 (D₀ ∩ D₁) (w n) (k n) := by
    apply (hwD₀ n).localize_compact_inter hD₁ (hf n).2.1 (hf n).2.2
    filter_upwards [hv0] with x hx
    intro hxK
    have hfx : f n x = 0 := image_eq_zero_of_notMem_tsupport hxK
    change Min.min (v x) (Max.max (f n x) 0) = 0
    rw [hfx, max_self, min_eq_right hx]
  have hzeroV : Tendsto (fun _ : ℕ => eLpNorm (fun x => v x - v x) 2 volume)
      atTop (𝓝 0) := by simp
  have hzeroG : Tendsto (fun _ : ℕ => eLpNorm (fun x => h x - h x) 2 volume)
      atTop (𝓝 0) := by simp
  have hp := hu₁A.tendsto_eLpNorm_pos_part hfA hfu hfg
  have hc := hvA.tendsto_eLpNorm_min hu₁A.pos_part (fun _ => hvA)
    (fun n => (hfA n).pos_part) hzeroV hzeroG hp.1 hp.2
  apply MemH10.of_tendsto hv.1 hv.2.1 hw
  · apply hc.1.congr'
    exact Eventually.of_forall fun n => eLpNorm_congr_ae (by
      filter_upwards [hvu₁] with x hx
      simp only [w, min_eq_left (hx.trans (le_max_left _ _))])
  · apply hc.2.congr'
    exact Eventually.of_forall fun n => eLpNorm_congr_ae (by
      filter_upwards [hvu₁] with x hx
      simp only [k, if_pos (hx.trans (le_max_left _ _))])

end Torsion
end

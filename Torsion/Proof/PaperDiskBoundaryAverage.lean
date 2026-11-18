module

public import Torsion.Definitions
public import Mathlib.MeasureTheory.Integral.CircleAverage

@[expose] public section

/-! # Circular exhaustion of a bounded domain in conformal coordinates -/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace Torsion

/-- Compact interior superlevel sets force a continuous zero-boundary
function to vanish uniformly in the outer annuli of a disk parametrization. -/
theorem diskChart_uniform_boundary {S : Set Plane} {F J : Plane → Plane} {U : Plane → ℝ}
    (hF : MapsTo F (ball 0 1) S) (hJ : MapsTo J S (ball 0 1))
    (hcJ : ContinuousOn J S) (hleft : LeftInvOn J F (ball 0 1))
    (hKcomp : ∀ e : ℝ, 0 < e →
      ∃ K : Set Plane, IsCompact K ∧ K ⊆ S ∧ ∀ w ∈ S, e ≤ |U w| → w ∈ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ z ∈ ball (0 : Plane) 1, r < ‖z‖ → |U (F z)| < ε := by
  obtain ⟨K,hK,hKD,hleK⟩ := hKcomp ε hε
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hm⟩ := hK.exists_isMaxOn hne (hcJ.norm.mono hKD)
    refine ⟨‖J x‖, norm_nonneg _, by simpa using hJ (hKD hx), ?_⟩
    intro z hzin hlarge
    by_contra! hu
    have hy : F z ∈ K := hleK _ (hF hzin) hu
    have hle : ‖J (F z)‖ ≤ ‖J x‖ := hm hy
    exact hlarge.not_ge (by simpa only [hleft hzin] using hle)
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro z hzin _
    exact lt_of_not_ge fun hu => hne ⟨F z, hleK _ (hF hzin) hu⟩

/-- The circular mean of the physical zero extension tends to zero as
centered disk coordinates exhaust the conformal image. -/
theorem diskChart_circleAverage_tendsto_zero {S : Set Plane} {F J : Plane → Plane} {U : Plane → ℝ}
    (hF : MapsTo F (ball 0 1) S) (hcF : ContinuousOn F (ball 0 1))
    (hJ : MapsTo J S (ball 0 1)) (hcJ : ContinuousOn J S)
    (hleft : LeftInvOn J F (ball 0 1)) (hc : ContinuousOn U S) (hKcomp : ∀ e : ℝ, 0 < e →
      ∃ K : Set Plane, IsCompact K ∧ K ⊆ S ∧ ∀ w ∈ S, e ≤ |U w| → w ∈ K) :
    Tendsto (fun r : ℝ => Real.circleAverage (U ∘ F) 0 r) (𝓝[<] 1) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨r₀,h0,h1,hs⟩ := diskChart_uniform_boundary hF hJ hcJ hleft hKcomp (half_pos hε)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds h1), self_mem_nhdsWithin] with r hrr hru
  have hr : 0 < r := lt_of_le_of_lt h0 hrr
  have hsp : sphere (0 : Plane) |r| ⊆ ball 0 1 := by
    intro z hzin
    change dist z 0 < 1
    rw [show dist z 0 = |r| from hzin, abs_of_pos hr]
    exact hru
  have hci : CircleIntegrable (fun z => |U (F z)|) 0 r :=
    ((hc.abs.comp hcF hF).mono hsp).circleIntegrable'
  have hb := Real.circleAverage_mono_on_of_le_circle hci (a := ε/2) (by
    intro z hzin
    have hn : ‖z‖ = r := by simpa [mem_sphere, abs_of_pos hr] using hzin
    exact (hs z (hsp hzin) (hn ▸ hrr)).le)
  rw [Real.dist_eq, sub_zero]
  exact (Real.abs_circleAverage_le_circleAverage_abs.trans hb).trans_lt (half_lt_self hε)

end Torsion

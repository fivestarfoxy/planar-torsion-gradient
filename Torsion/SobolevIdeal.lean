module

public import Torsion.SobolevLocalization
public import Torsion.SobolevMinContinuity
public import Torsion.BoundedDomains

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The zero-boundary Sobolev ideal property

This is the one-domain admissibility assertion of Lemma 3.2. Its proof uses
compact smooth approximants, strong H¹ continuity of minimum, and a genuine
compact cutoff. No characterization by vanishing outside an open set is used.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Torsion

/-- If 0≤v≤u and u has zero trace on D, then v has zero trace on D too.
All inequalities concern actual almost-everywhere representatives. -/
theorem MemH10.of_nonneg_le {D E : Set Plane}
    {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : MemH10 D u g) (hv : MemH10 E v h) (hD : IsOpen D)
    (hv0 : ∀ᵐ x ∂volume, 0 ≤ v x) (hvu : ∀ᵐ x ∂volume, v x ≤ u x) :
    MemH10 D v h := by
  classical
  let B := E ∪ D
  have hvB : MemH10 B v h := hv.mono subset_union_left
  have huB : MemH10 B u g := hu.mono subset_union_right
  obtain ⟨_, _, f, hf, hfu, hfg⟩ := hu
  have hfB (n : ℕ) : MemH10 B (f n) (gradient (f n)) :=
    (hf n).memH10.mono subset_union_right
  let w : ℕ → Plane → ℝ := fun n x => Min.min (v x) (f n x)
  let k : ℕ → Plane → Plane := fun n x => if v x ≤ f n x then h x else gradient (f n) x
  have hw (n : ℕ) : MemH10 D (w n) (k n) := by
    apply (hvB.min (hfB n)).localize_compact_value hD (hf n).2.1 (hf n).2.2
    filter_upwards [hv0] with x hx
    intro hxK
    have hfx : f n x = 0 := image_eq_zero_of_nmem_tsupport hxK
    simp only [hfx, min_eq_right hx]
  have hzeroV : Tendsto (fun _ : ℕ => eLpNorm (fun x => v x - v x) 2 volume)
      atTop (𝓝 0) := by simp
  have hzeroG : Tendsto (fun _ : ℕ => eLpNorm (fun x => h x - h x) 2 volume)
      atTop (𝓝 0) := by simp
  have hc := hvB.tendsto_eLpNorm_min huB (fun _ => hvB) hfB hzeroV hzeroG hfu hfg
  apply MemH10.of_tendsto hv.1 hv.2.1 hw
  · apply hc.1.congr'
    exact Eventually.of_forall fun n => eLpNorm_congr_ae (by
      filter_upwards [hvu] with x hx
      simp only [w, min_eq_left hx])
  · apply hc.2.congr'
    exact Eventually.of_forall fun n => eLpNorm_congr_ae (by
      filter_upwards [hvu] with x hx
      simp only [k, if_pos hx])

end Torsion
end

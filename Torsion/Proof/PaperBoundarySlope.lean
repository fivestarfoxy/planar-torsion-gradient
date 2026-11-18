module

public import Torsion.Definitions
public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-! # The one-sided first-order expansion at a smooth marked point -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace Torsion

/-- At any boundary point where the zero-boundary solution has a differential
from inside, the inward unit normal derivative gives the first-order term.
The ray only needs to enter the domain locally. -/
theorem twice_boundary_normal_expansion {D : Set Plane} {u : Plane → ℝ}
    {p n : Plane} {L : Plane →L[ℝ] ℝ} (hu : HasFDerivWithinAt u L (closure D) p)
    (hzero : u p = 0) (hn : ‖n‖ = 1)
    (hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), p + t • n ∈ D) :
    (fun t : ℝ => 2 * u (p + t • n) - 2 * t * L n) =o[𝓝[>] 0] fun t => t := by
  have hlim : Tendsto (fun t : ℝ => p + t • n) (𝓝[>] 0) (𝓝[closure D] p) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hray.mono fun _ h => subset_closure h⟩
    have hc : Continuous (fun t : ℝ => p + t • n) := continuous_const.add (continuous_id.smul continuous_const)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hrem := hu.isLittleO.comp_tendsto hlim
  have hid : (fun t : ℝ => p + t • n - p) =O[𝓝[>] (0 : ℝ)] fun t => t := by
    apply isBigO_iff.mpr
    refine ⟨1, Eventually.of_forall fun t => ?_⟩
    simp [hn]
  have h := (hrem.trans_isBigO hid).const_mul_left 2
  convert h using 1
  funext t
  simp only [Function.comp_apply, add_sub_cancel_left, map_smul, smul_eq_mul, hzero, sub_zero]
  ring

end Torsion

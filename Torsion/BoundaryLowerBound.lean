import Torsion.Definitions
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# Passing an interior essential gradient bound to a boundary limit

This proves the measure-theoretic step used for the marked-gradient lower
bound. It does not presume that a boundary maximum exists, and the norm is
always the interior essential supremum. Existence of a continuous boundary
representative is an analytic regularity question, separate from this step.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Torsion

/-- The inward derivative of a representative vanishing at the marked point
is the marked quotient limit in Definition 3.1. -/
theorem hasMarkedFlux_of_normal_derivative {u : Plane → ℝ} {q : ℝ}
    (hu : u 0 = 0)
    (hd : HasDerivAt (fun t : ℝ => u ((t : ℂ) * Complex.I)) q 0) :
    HasMarkedFlux u q := by
  have h := hd.tendsto_slope_zero_right
  simpa [HasMarkedFlux, hu, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- A marked flux, when constructed, is unique. -/
theorem HasMarkedFlux.unique {u : Plane → ℝ} {q r : ℝ}
    (hq : HasMarkedFlux u q) (hr : HasMarkedFlux u r) : q = r :=
  tendsto_nhds_unique hq hr

/-- A continuous representative on an open planar domain is bounded pointwise
by its interior essential supremum. Null exceptional sets cannot contain a
nonempty open set. -/
theorem enorm_le_eLpNorm_top_on_open {D : Set Plane} (hD : IsOpen D)
    {g : Plane → Plane} (hg : ContinuousOn g D) {x : Plane} (hx : x ∈ D) :
    ‖g x‖ₑ ≤ eLpNorm g ∞ (volume.restrict D) := by
  let C := eLpNorm g ∞ (volume.restrict D)
  have hae : (fun z => max ‖g z‖ₑ C) =ᵐ[volume.restrict D] (fun _ => C) := by
    filter_upwards [enorm_ae_le_eLpNormEssSup g (volume.restrict D)] with z hz
    exact max_eq_right hz
  have hcont : ContinuousOn (fun z => max ‖g z‖ₑ C) D :=
    hg.enorm.sup continuousOn_const
  have heq := Measure.eqOn_open_of_ae_eq hae hD hcont continuousOn_const
  exact max_eq_right_iff.mp (heq hx)

/-- The same bound holds for a continuous boundary limit at any point in the
closure of the domain. This is the final step in comparing Q with G. -/
theorem boundary_enorm_le_eLpNorm_top {D : Set Plane} (hD : IsOpen D)
    {g : Plane → Plane} {p : Plane}
    (hg : ContinuousOn g D) (hgp : ContinuousWithinAt g D p) (hp : p ∈ closure D) :
    ‖g p‖ₑ ≤ eLpNorm g ∞ (volume.restrict D) := by
  haveI : NeBot (𝓝[D] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  apply isClosed_Iic.mem_of_tendsto hgp.enorm
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact enorm_le_eLpNorm_top_on_open hD hg hx

/-- A scalar inward component of a continuous boundary gradient is therefore
bounded by the essential supremum. In particular one may take its imaginary
component at the marked flat point. -/
theorem boundary_im_le_eLpNorm_top {D : Set Plane} (hD : IsOpen D)
    {g : Plane → Plane} {p : Plane}
    (hg : ContinuousOn g D) (hgp : ContinuousWithinAt g D p) (hp : p ∈ closure D) :
    ENNReal.ofReal (g p).im ≤ eLpNorm g ∞ (volume.restrict D) := by
  apply le_trans (ENNReal.ofReal_le_ofReal (Complex.im_le_norm _))
  simpa only [ofReal_norm_eq_enorm] using boundary_enorm_le_eLpNorm_top hD hg hgp hp

end Torsion
end

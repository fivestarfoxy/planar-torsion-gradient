import Torsion.CanonicalSupportingFlux
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Actual inward normal rays in regular sublevel domains -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Torsion

/-- A negative directional derivative at a level point makes the actual
positive vertical ray enter the strict sublevel for all sufficiently small
positive parameters. -/
theorem eventually_vertical_mem_sublevel {F : Plane → ℝ} {L : Plane →L[ℝ] ℝ} {c : ℝ}
    (hF : HasFDerivAt F L 0) (hlevel : F 0 = c) (hdir : L Complex.I < 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (t : ℂ) * Complex.I ∈ {z | F z < c} := by
  have hline : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const Complex.I
  have hF' : HasFDerivAt F L ((0 : ℂ) * Complex.I) := by simpa using hF
  have hd : HasDerivAt (fun t : ℝ => F ((t : ℂ) * Complex.I)) (L Complex.I) 0 :=
    hF'.comp_hasDerivAt 0 hline
  have hneg := hd.tendsto_slope_zero_right.eventually (Iio_mem_nhds hdir)
  filter_upwards [hneg, self_mem_nhdsWithin] with t ht ht0
  have hquot : (F ((t : ℂ) * Complex.I) - c) / t < 0 := by
    simpa [slope_def_field, hlevel, div_eq_mul_inv, mul_comm] using ht
  have hh := (div_lt_iff₀ ht0).mp hquot
  simpa only [zero_mul, sub_lt_zero] using hh

/-- On an actual regular sublevel, the supporting quotient comparison has
no separate ray-entry premise. -/
theorem HasMarkedFlux.le_second_spectral_bound_of_sublevel
    {D : ConvexDomain} {u : Plane → ℝ} {g : Plane → Plane} {q c : ℝ}
    {F : Plane → ℝ} {L : Plane →L[ℝ] ℝ}
    (hq : HasMarkedFlux u q) (hu : IsWeakTorsion D.carrier u g)
    (huc : ContinuousOn u D.carrier) (hzero : (0 : Plane) ∈ closure D.carrier)
    (hhalf : D.carrier ⊆ upperHalfPlane) (hD : D.carrier = {z | F z < c})
    (hF : HasFDerivAt F L 0) (hlevel : F 0 = c) (hdir : L Complex.I < 0) :
    q ≤ Spectral.spectralConstant Spectral.secondEigenvalue Spectral.secondEigenfunction *
      Real.sqrt D.area := by
  apply hq.le_second_spectral_bound hu huc hzero hhalf
  rw [hD]
  exact eventually_vertical_mem_sublevel hF hlevel hdir

end Torsion

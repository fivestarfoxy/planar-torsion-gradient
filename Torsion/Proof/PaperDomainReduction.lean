module

public import Torsion.Proof.PaperBoundaryAttainment
public import Torsion.ConvexSupportingRadial
public import Mathlib.Analysis.Convex.Measure

@[expose] public section

/-! # The reduction from arbitrary convex domains to radial observations -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace Torsion

/-- Lemma 5.2, including the flat half-ball with the very same radius as the
outer thickening and the full one-sided limit in physical planar measure. -/
theorem ConvexDomain.supporting_radial_outer_approximation (D : ConvexDomain)
    (hzero : (0 : Plane) ∈ closure D.carrier) (hhalf : D.carrier ⊆ upperHalfPlane) :
    (∀ δ : ℝ, 0 < δ → ∃ R : ContinuousProfiles.Profile, (∀ θ, 0 < R θ) ∧
      D.carrier ⊆ radialDomain (ContinuousProfiles.extend R) ∧
      radialDomain (ContinuousProfiles.extend R) = thickening δ D.carrier ∩ upperHalfPlane ∧
      ball (0 : Plane) δ ∩ upperHalfPlane ⊆ radialDomain (ContinuousProfiles.extend R)) ∧
    Tendsto (fun δ : ℝ => volume (thickening δ D.carrier ∩ upperHalfPlane))
      (𝓝[>] 0) (𝓝 (volume D.carrier)) := by
  constructor
  · intro δ hδ
    refine ⟨supportingRadialProfile D hzero δ hδ, supportingRadialProfile_pos D hzero hδ,
      subset_radialDomain_supportingRadialProfile D hzero hhalf hδ,
      radialDomain_supportingRadialProfile D hzero hδ, ?_⟩
    rw [radialDomain_supportingRadialProfile]
    apply inter_subset_inter_left
    rw [← thickening_closure]
    exact ball_subset_thickening hzero δ
  · have hlim := tendsto_measure_thickening (μ := (volume : Measure Plane)) (s := D.carrier)
        ⟨1, zero_lt_one, D.bounded.thickening.measure_lt_top.ne⟩
    rw [measure_closure_of_null_frontier (D.convex.addHaar_frontier volume)] at hlim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact measure_mono (subset_inter (self_subset_thickening hδ D.carrier) hhalf)
    · exact Eventually.of_forall fun _ => measure_mono inter_subset_left

/-- Proposition 5.4 for every coefficient satisfying the radial comparison.
The maximizing normal frame belongs to the original weak torsion solution. -/
theorem DirichletTheory.G_le_of_positive_radial_bound (T : DirichletTheory) (D : ConvexDomain)
    {C : ℝ} (hbound : ∀ R : ContinuousProfiles.Profile, (∀ θ, 0 < R θ) →
      torsionFlux (radialDomain (ContinuousProfiles.extend R)) ≤
        C * Real.sqrt (radialArea (ContinuousProfiles.extend R))) :
    T.G D ≤ ENNReal.ofReal (C * Real.sqrt D.area) := by
  obtain ⟨U, p, n, hc, hweak, _, _, hp, hn, hsup, hline, hlim⟩ :=
    T.exists_maximizing_normal_quotient D
  let e := normalFrame n hn
  let E := D.inNormalFrame p n hn
  let V (z : Plane) := U (e z + p)
  have hcoord (t : ℝ) : e ((t : Plane) * Complex.I) + p = p + t • n := by
    rw [← Complex.real_smul, map_smul, show e Complex.I = n from normalFrame_I n hn, add_comm]
  have hq : HasMarkedFlux V (T.G D).toReal := by
    simpa only [HasMarkedFlux, V, hcoord] using hlim
  have hline' : ∀ᶠ t : ℝ in 𝓝[>] 0, (t : Plane) * Complex.I ∈ E.carrier := by
    filter_upwards [hline] with t ht
    apply (D.mem_inNormalFrame p n _ hn).mpr
    change e ((t : Plane) * Complex.I) + p ∈ D.carrier
    rwa [hcoord]
  have hrep : Continuous V := hc.comp (e.continuous.add continuous_const)
  have h := hq.le_of_positive_radial_bound (hweak.inNormalFrame p n hn)
    hrep.continuousOn (D.zero_mem_closure_inNormalFrame p n hn (frontier_subset_closure hp))
    (D.inNormalFrame_subset_upper p n hn hsup) hline' hbound
  rw [D.inNormalFrame_area] at h
  rw [← ENNReal.ofReal_toReal (T.G_lt_top D).ne]
  exact ENNReal.ofReal_le_ofReal h

/-- The inward-maximizer implication used in Section 6: a domain attaining
the sharp normalized bound dominates the gradient norm of each convex
subdomain in its original physical scale. -/
theorem DirichletTheory.G_subdomain_le_of_attaining (T : DirichletTheory) {D : ConvexDomain}
    (hD : T.G D = ENNReal.ofReal
      (Spectral.spectralConstant Spectral.secondEigenvalue Spectral.secondEigenfunction *
        Real.sqrt D.area)) (E : ConvexDomain) (hED : E.carrier ⊆ D.carrier) : T.G E ≤ T.G D := by
  rw [hD]
  apply (T.G_le_second_spectral_bound E).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ Spectral.secondMoments.sharpConstant_pos.le
  apply Real.sqrt_le_sqrt
  exact ENNReal.toReal_mono D.bounded.measure_lt_top.ne (measure_mono hED)

end Torsion

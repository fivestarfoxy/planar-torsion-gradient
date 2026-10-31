module

public import Torsion.CanonicalUniversal

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Marked outer observations for the original gradient norm

For every fixed positive hull radius, every strict lower bound for the
original weak-gradient norm is exceeded by the actual marked flux of a
flat outer hull in a supporting normal frame. The supporting frame may
depend on the threshold. No maximizing boundary derivative or
boundary-attainment theorem is assumed: the proof retains the marked flux
in the uniform Taylor comparison and uses the proved boundary-collar
control of the gradient.

This is the analytic bridge toward full-domain stability. It does not yet
assert symmetric-difference stability or equality classification.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal ContDiff

namespace Torsion

/-- The pointwise comparison retains the actual outer marked flux, rather
than replacing it by a spectral upper bound. The remainder is uniform over
all marked domains with the stated common patch and slab height. -/
theorem exists_uniform_marked_flux_collar_comparison_constant {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {D E : ConvexDomain} {u U : Plane → ℝ}
      {g : Plane → Plane} {b : ℝ},
      IsWeakTorsion D.carrier u g → ContinuousOn U D.carrier →
      (u =ᵐ[volume.restrict D.carrier] U) → D.carrier ⊆ E.carrier →
      IsMarked E.carrier → 0 ≤ b →
      upperHalfPlane ∩ Metric.ball (0 : Plane) (4*r) ⊆ E.carrier →
      (∀ z ∈ E.carrier, z.im < b) →
      ∀ t : ℝ, 0 < t → t < r/2 → (t : Plane)*Complex.I ∈ D.carrier →
        U ((t : Plane)*Complex.I) ≤
          (torsionFlux E.carrier + (C*(2*r*b+8*r^2)+1/2)*t)*t := by
  obtain ⟨C, hC, hTaylor⟩ :=
    exists_uniform_slab_marked_torsion_normal_quotient_constant_on_representative hr
  refine ⟨C, hC, ?_⟩
  intro D E u U g b hu hU hUrep hDE hE hb hhalf hheight t ht htR htD
  obtain ⟨v⟩ := HilbertDirichlet.exists_dirichletSolution_of_bounded E.isOpen.measurableSet E.bounded
  have hv := v.weakEquation
  obtain ⟨W, hW, hWzero, hWrep, hWG⟩ := hv.exists_smooth_representative E.isOpen E.bounded
  have hcompare := hu.le_on_continuous_representatives hv D.isOpen E.isOpen
    D.bounded E.bounded hDE hU hW.continuousOn hUrep hWrep
  have herror := hTaylor hE hv hb hhalf hheight hW.continuousOn hWrep t ht htR
  apply (hcompare _ htD).trans
  apply (div_le_iff₀ ht).mp
  have herr := (le_abs_self (W ((t : Plane)*Complex.I)/t-torsionFlux E.carrier)).trans herror
  linarith

/-- A bound on the actual marked fluxes of the fixed-radius supporting
flat hulls gives a uniform boundary collar on the original convex domain.
This intermediate comparison is used below with the negation of an
existential flux witness; its flux bound is not a final theorem premise. -/
theorem IsWeakTorsion.boundary_collar_of_supporting_flatHull_flux_bound
    {D : ConvexDomain} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D.carrier u g) (hc : Continuous U)
    (hrep : u =ᵐ[volume.restrict D.carrier] U) (hzero : ∀ x ∉ D.carrier, U x = 0)
    {r L ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hflux : ∀ p ∈ frontier D.carrier, ∀ n : Plane, ∀ hn : ‖n‖ = 1,
      (∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) n (z-p)) →
      torsionFlux ((D.inNormalFrame p n hn).flatHull r).carrier ≤ L) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ D.carrier, infDist x D.carrierᶜ < δ →
      U x ≤ (L+ε)*infDist x D.carrierᶜ := by
  have hweak := hu.of_zero_extension_representative D.isOpen.measurableSet hrep hzero
  obtain ⟨a, h, M, hh, hM, ha, hball, hsupport⟩ := D.exists_uniform_support_inball
  obtain ⟨R, hR, hRD⟩ := D.bounded.closure.subset_ball_lt 0 (0 : Plane)
  let b : ℝ := 2*R+1
  have hb : 0 ≤ b := by dsimp [b]; linarith
  let ρ : ℝ := flatHullPatchRadius r h M / 4
  have hρ : 0 < ρ := div_pos (flatHullPatchRadius_pos hr hh hM) (by norm_num)
  obtain ⟨C, hC, hcompare⟩ := exists_uniform_marked_flux_collar_comparison_constant hρ
  let K : ℝ := C*(2*ρ*b+8*ρ^2)+1/2
  have hK : 0 < K := by dsimp [K]; positivity
  let δ : ℝ := min (ρ/2) (ε/(K+1))
  have hδ : 0 < δ := lt_min (half_pos hρ) (div_pos hε (by positivity))
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxδ
  obtain ⟨p, hp, hd, hnorm, hn, hs⟩ := D.exists_nearest_supported_frontier hx
  let d : ℝ := infDist x D.carrierᶜ
  let n : Plane := d⁻¹ • (x-p)
  let e := normalFrame n hn
  let E := D.inNormalFrame p n hn
  let F := E.flatHull r
  let a' : Plane := e.symm (a-p)
  obtain ⟨hheight, hdisplacement⟩ := hsupport p hp n hn hs
  obtain ⟨ha', hball', hheight', hnorm'⟩ :=
    D.inNormalFrame_inball_bounds p n a hn hh hball hheight hdisplacement
  have hhalf : E.carrier ⊆ upperHalfPlane := D.inNormalFrame_subset_upper p n hn hs
  have hDE : E.carrier ⊆ F.carrier := subset_flatOuterHull E.isOpen r
  have hmarked : IsMarked F.carrier :=
    flatOuterHull_isMarked E.isOpen E.bounded hhalf E.nonempty hr
  have hpatch : upperHalfPlane ∩ ball (0 : Plane) (4*ρ) ⊆ F.carrier := by
    simp only [F, ConvexDomain.flatHull_carrier]
    convert halfBall_subset_flatOuterHull_of_point_bounds E.isOpen ha' hr hh hM hheight' hnorm' using 1
    dsimp [ρ]
    ring_nf
  have hupper : ∀ z ∈ E.carrier, z.im ≤ b := by
    intro z hz
    have hzD := (D.mem_inNormalFrame p n z hn).mp hz
    have hzR : ‖e z+p‖ < R := by
      simpa only [mem_ball, dist_zero_right] using hRD (subset_closure hzD)
    have hpR : ‖p‖ < R := by
      simpa only [mem_ball, dist_zero_right] using hRD (frontier_subset_closure hp)
    have hzbound : ‖z‖ < 2*R := by
      calc
        ‖z‖ = ‖e z‖ := (e.norm_map z).symm
        _ = ‖(e z+p)-p‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖e z+p‖ + ‖p‖ := norm_sub_le _ _
        _ < 2*R := by linarith
    exact (Complex.im_le_norm z).trans (hzbound.le.trans (by dsimp [b]; linarith))
  have hFheight : ∀ z ∈ F.carrier, z.im < b :=
    flatOuterHull_subset_upper_height hb hupper r
  have hpoint : e ((d : Plane)*Complex.I) + p = x := by
    rw [← Complex.real_smul, map_smul, normalFrame_I]
    change d • (d⁻¹ • (x-p)) + p = x
    rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul, sub_add_cancel]
  have hline : (d : Plane)*Complex.I ∈ E.carrier := by
    apply (D.mem_inNormalFrame p n _ hn).mpr
    change e ((d : Plane)*Complex.I) + p ∈ D.carrier
    rwa [hpoint]
  have hcE : ContinuousOn (fun z => U (e z+p)) E.carrier :=
    (hc.comp (e.continuous.add continuous_const)).continuousOn
  have hdsmall : d < ρ/2 := hxδ.trans_le (min_le_left _ _)
  have hnormal := hcompare (hweak.inNormalFrame p n hn) hcE EventuallyEq.rfl
    hDE hmarked hb hpatch hFheight d hd hdsmall hline
  change U (e ((d : Plane)*Complex.I)+p) ≤ (torsionFlux F.carrier+K*d)*d at hnormal
  rw [hpoint] at hnormal
  have hKd : K*d ≤ ε := by
    have htbound : d < ε/(K+1) := hxδ.trans_le (min_le_right _ _)
    have hm := (lt_div_iff₀ (show 0 < K+1 by positivity)).mp htbound
    nlinarith
  apply hnormal.trans
  apply mul_le_mul_of_nonneg_right _ hd.le
  exact add_le_add (hflux p hp n hn hs) hKd

/-- Every strict lower bound for the original weak-gradient norm is
exceeded by an actual marked flux of a supporting flat outer hull. The
radius is arbitrary and fixed in advance, so it may be taken as small as
needed for the separately proved geometric outer approximation. -/
theorem DirichletTheory.exists_supporting_flatHull_flux_gt
    (T : DirichletTheory) (D : ConvexDomain) {r : ℝ} (hr : 0 < r)
    {L : ℝ≥0} (hL : (L : ℝ≥0∞) < T.G D) :
    ∃ p ∈ frontier D.carrier, ∃ n : Plane, ∃ hn : ‖n‖ = 1,
      (∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) n (z-p)) ∧
      (L : ℝ) < torsionFlux ((D.inNormalFrame p n hn).flatHull r).carrier := by
  by_contra hnone
  push Not at hnone
  have hu := (T.solution D).weakEquation
  obtain ⟨U, hc, hs, hz, hp, hrep, hg⟩ := hu.exists_continuous_smooth_representative
  have hbound := hu.gradient_bound_of_boundary_collar_approx D.isOpen D.bounded
    hc hs hg hrep hz hp (L := L) (fun ε hε =>
      hu.boundary_collar_of_supporting_flatHull_flux_bound hc hrep hz hr hε hnone)
  exact (not_lt_of_ge hbound) hL

/-- A near-maximal observation can be chosen on an actual positive
continuous radial outer domain. Both approximation radii are prescribed in
advance, and its metric excess is at most their explicit sum. This form
feeds directly into the proved continuous-profile calibration and deficit. -/
theorem DirichletTheory.exists_supporting_positive_radial_flux_gt
    (T : DirichletTheory) (D : ConvexDomain) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    {L : ℝ≥0} (hL : (L : ℝ≥0∞) < T.G D) :
    ∃ p ∈ frontier D.carrier, ∃ n : Plane, ∃ hn : ‖n‖ = 1,
      ∃ R : ContinuousProfiles.Profile,
        (∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) n (z-p)) ∧
        (∀ θ, 0 < R θ) ∧
        Convex ℝ (radialDomain (ContinuousProfiles.extend R)) ∧
        (D.inNormalFrame p n hn).carrier ⊆ radialDomain (ContinuousProfiles.extend R) ∧
        radialDomain (ContinuousProfiles.extend R) ⊆
          thickening (2*r+δ) (D.inNormalFrame p n hn).carrier ∧
        (L : ℝ) < torsionFlux (radialDomain (ContinuousProfiles.extend R)) := by
  obtain ⟨p, hp, n, hn, hs, hq⟩ := T.exists_supporting_flatHull_flux_gt D hr hL
  let E := D.inNormalFrame p n hn
  let F := E.flatHull r
  have hEhalf : E.carrier ⊆ upperHalfPlane := D.inNormalFrame_subset_upper p n hn hs
  have hEzero : (0 : Plane) ∈ closure E.carrier :=
    D.zero_mem_closure_inNormalFrame p n hn (frontier_subset_closure hp)
  have hEF : E.carrier ⊆ F.carrier := subset_flatOuterHull E.isOpen r
  have hFmarked : IsMarked F.carrier :=
    flatOuterHull_isMarked E.isOpen E.bounded hEhalf E.nonempty hr
  have hFzero : (0 : Plane) ∈ closure F.carrier := closure_mono hEF hEzero
  let R := supportingRadialProfile F hFzero δ hδ
  have hRpos : ∀ θ, 0 < R θ := supportingRadialProfile_pos F hFzero hδ
  have hFR : F.carrier ⊆ radialDomain (ContinuousProfiles.extend R) :=
    subset_radialDomain_supportingRadialProfile F hFzero hFmarked.2.2.1 hδ
  have hRconvex : Convex ℝ (radialDomain (ContinuousProfiles.extend R)) := by
    change Convex ℝ (radialDomain
      (ContinuousProfiles.extend (supportingRadialProfile F hFzero δ hδ)))
    rw [radialDomain_supportingRadialProfile]
    exact (F.convex.thickening δ).inter (convex_halfSpace_im_gt 0)
  refine ⟨p, hp, n, hn, R, hs, hRpos, hRconvex, hEF.trans hFR, ?_, ?_⟩
  · intro z hz
    have hzouter : z ∈ thickening δ F.carrier := by
      change z ∈ radialDomain
        (ContinuousProfiles.extend (supportingRadialProfile F hFzero δ hδ)) at hz
      rw [radialDomain_supportingRadialProfile] at hz
      exact hz.1
    obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.mp hzouter
    obtain ⟨x, hx, hyx⟩ := mem_thickening_iff.mp
      (flatOuterHull_subset_thickening E.convex hEzero hr hy)
    apply mem_thickening_iff.mpr
    refine ⟨x, hx, ?_⟩
    have hd := (dist_triangle z y x).trans_lt (add_lt_add hzy hyx)
    linarith
  · exact hq.trans_le (torsionFlux_mono hFmarked
      (ContinuousProfiles.domain_isMarked hRpos) hFR)

end Torsion

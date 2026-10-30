import Torsion.ConvexGaugeRadial
import Torsion.MarkedFlux

/-!
# Radial outer comparison at supporting boundary points

Metric thickening supplies a full convex neighborhood of the supporting
origin. Its gauge profile is positive at both joins, contains the original
upper-half-plane domain, and has area tending to the original area. This
implements the boundary-to-radial comparison without a degenerate profile.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Pointwise Topology
namespace Torsion

/-- The actual metric thickening of a convex domain. -/
def ConvexDomain.gaugeOuterThickening (D : ConvexDomain) (δ : ℝ) (hδ : 0 < δ) :
    ConvexDomain where
  carrier := thickening δ D.carrier
  isOpen := isOpen_thickening
  bounded := D.bounded.thickening
  convex := D.convex.thickening δ
  nonempty := D.nonempty.mono (self_subset_thickening hδ D.carrier)

/-- A supporting boundary point belongs to every full outer thickening. -/
theorem zero_mem_gaugeOuterThickening (D : ConvexDomain)
    (hzero : (0 : Plane) ∈ closure D.carrier) {δ : ℝ} (hδ : 0 < δ) :
    (0 : Plane) ∈ (D.gaugeOuterThickening δ hδ).carrier :=
  closure_subset_thickening hδ D.carrier hzero

/-- An actual positive radial outer profile at the supporting origin. -/
def supportingRadialProfile (D : ConvexDomain) (hzero : (0 : Plane) ∈ closure D.carrier)
    (δ : ℝ) (hδ : 0 < δ) : ContinuousProfiles.Profile :=
  convexGaugeProfile (D.gaugeOuterThickening δ hδ) (zero_mem_gaugeOuterThickening D hzero hδ)

theorem supportingRadialProfile_pos (D : ConvexDomain)
    (hzero : (0 : Plane) ∈ closure D.carrier) {δ : ℝ} (hδ : 0 < δ)
    (θ : ContinuousProfiles.Angle) : 0 < supportingRadialProfile D hzero δ hδ θ :=
  convexGaugeProfile_pos _ _ θ

/-- Exact identification of the positive radial outer domain. -/
theorem radialDomain_supportingRadialProfile (D : ConvexDomain)
    (hzero : (0 : Plane) ∈ closure D.carrier) {δ : ℝ} (hδ : 0 < δ) :
    radialDomain (ContinuousProfiles.extend (supportingRadialProfile D hzero δ hδ)) =
      thickening δ D.carrier ∩ upperHalfPlane :=
  radialDomain_convexGaugeProfile _ _

/-- Supporting-half-plane competitors are contained in the positive radial
outer domains, including competitors with curved boundary at the origin. -/
theorem subset_radialDomain_supportingRadialProfile (D : ConvexDomain)
    (hzero : (0 : Plane) ∈ closure D.carrier) (hhalf : D.carrier ⊆ upperHalfPlane)
    {δ : ℝ} (hδ : 0 < δ) :
    D.carrier ⊆ radialDomain (ContinuousProfiles.extend (supportingRadialProfile D hzero δ hδ)) := by
  rw [radialDomain_supportingRadialProfile]
  exact subset_inter (self_subset_thickening hδ D.carrier) hhalf

/-- Actual angular radial area tends to the original convex-domain area.
The upper domains need not have a smooth radial boundary. -/
theorem radialArea_supportingRadialProfile_tendsto (D : ConvexDomain)
    (hzero : (0 : Plane) ∈ closure D.carrier) (hhalf : D.carrier ⊆ upperHalfPlane)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => radialArea (ContinuousProfiles.extend
      (supportingRadialProfile D hzero (δ n) (hδ n)))) atTop (𝓝 D.area) := by
  let E : ℕ → ConvexDomain := fun n => D.gaugeOuterThickening (δ n) (hδ n)
  have hEarea : Tendsto (fun n => (E n).area) atTop (𝓝 D.area) :=
    D.area_tendsto_of_outer_approximation E δ hδ hδlim
      (fun n => self_subset_thickening (hδ n) D.carrier) (fun _ => Subset.rfl)
  have harea (n : ℕ) : radialArea (ContinuousProfiles.extend
      (supportingRadialProfile D hzero (δ n) (hδ n))) =
      (volume (radialDomain (ContinuousProfiles.extend
        (supportingRadialProfile D hzero (δ n) (hδ n))))).toReal := by
    rw [← ContinuousProfiles.profileArea_embed]
    exact (ContinuousProfiles.geometric_area_eq_profileArea
      (supportingRadialProfile_pos D hzero (hδ n))).symm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hEarea
  · intro n
    dsimp only
    rw [harea n]
    exact ENNReal.toReal_mono
      (ContinuousProfiles.domain_isMarked (supportingRadialProfile_pos D hzero (hδ n))).2.1.measure_lt_top.ne
      (measure_mono (subset_radialDomain_supportingRadialProfile D hzero hhalf (hδ n)))
  · intro n
    dsimp only
    rw [harea n]
    apply ENNReal.toReal_mono (E n).bounded.measure_lt_top.ne
    apply measure_mono
    rw [radialDomain_supportingRadialProfile]
    exact inter_subset_left

/-- A sharp bound on all actual positive radial fluxes bounds every genuine
supporting-boundary quotient of every convex competitor. All radial geometry
and the limiting area passage are constructed, rather than assumed. -/
theorem HasTorsionFlux.le_of_positive_radial_bound {D : ConvexDomain} {q C : ℝ}
    (hq : HasTorsionFlux D.carrier q) (hzero : (0 : Plane) ∈ closure D.carrier)
    (hhalf : D.carrier ⊆ upperHalfPlane)
    (hbound : ∀ (R : ContinuousProfiles.Profile), (∀ θ, 0 < R θ) →
      torsionFlux (radialDomain (ContinuousProfiles.extend R)) ≤
        C * Real.sqrt (radialArea (ContinuousProfiles.extend R))) :
    q ≤ C * Real.sqrt D.area := by
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  let R : ℕ → ContinuousProfiles.Profile := fun n => supportingRadialProfile D hzero (δ n) (hδ n)
  have hR (n : ℕ) : ∀ θ, 0 < R n θ := supportingRadialProfile_pos D hzero (hδ n)
  have harea : Tendsto (fun n => radialArea (ContinuousProfiles.extend (R n))) atTop (𝓝 D.area) :=
    radialArea_supportingRadialProfile_tendsto D hzero hhalf δ hδ
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n => C * Real.sqrt (radialArea (ContinuousProfiles.extend (R n))))
      atTop (𝓝 (C * Real.sqrt D.area)) := tendsto_const_nhds.mul harea.sqrt
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [] with n
  have hm := ContinuousProfiles.domain_isMarked (hR n)
  exact (hq.mono (torsionFlux_spec hm) D.isOpen hm.1 D.bounded hm.2.1
    (subset_radialDomain_supportingRadialProfile D hzero hhalf (hδ n))).trans (hbound (R n) (hR n))

/-- The boundary quotient comparison needs continuity only inside the
original domain and eventual entry of the marked normal ray. No global
boundary-gradient representative is required for this passage. -/
theorem HasMarkedFlux.le_of_weakTorsion_subset_marked
    {D E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} {q p : ℝ}
    (hq : HasMarkedFlux u q) (hu : IsWeakTorsion D u g)
    (huc : ContinuousOn u D) (hD : IsOpen D) (hbD : Bornology.IsBounded D)
    (hhalf : D ⊆ upperHalfPlane) (hE : IsMarked E) (hDE : D ⊆ E)
    (hp : HasTorsionFlux E p)
    (hline : ∀ᶠ t : ℝ in 𝓝[>] 0, (t : ℂ) * Complex.I ∈ D) : q ≤ p := by
  obtain ⟨v, h, r, hv, hr, hvc, hvq⟩ := hp
  have hpoint := leOn_open_of_ae_le (hD.inter isOpen_ball)
    (huc.mono inter_subset_left)
    (hvc.mono (show D ∩ ball 0 r ⊆ upperHalfPlane ∩ ball 0 r from
      fun z hz => ⟨hhalf hz.1, hz.2⟩))
    (hu.mono hv hD hE.1 hbD hE.2.1 hDE)
  apply le_of_tendsto_of_tendsto hq hvq
  filter_upwards [hline, eventually_vertical_mem_halfBall hr, self_mem_nhdsWithin] with t ht htr ht0
  exact div_le_div_of_nonneg_right (hpoint _ ⟨ht, htr.2⟩) ht0.le

/-- Interior continuity and a genuine inward normal quotient suffice for
the full sharp radial comparison on a convex competitor. -/
theorem HasMarkedFlux.le_of_positive_radial_bound
    {D : ConvexDomain} {u : Plane → ℝ} {g : Plane → Plane} {q C : ℝ}
    (hq : HasMarkedFlux u q) (hu : IsWeakTorsion D.carrier u g)
    (huc : ContinuousOn u D.carrier) (hzero : (0 : Plane) ∈ closure D.carrier)
    (hhalf : D.carrier ⊆ upperHalfPlane)
    (hline : ∀ᶠ t : ℝ in 𝓝[>] 0, (t : ℂ) * Complex.I ∈ D.carrier)
    (hbound : ∀ (R : ContinuousProfiles.Profile), (∀ θ, 0 < R θ) →
      torsionFlux (radialDomain (ContinuousProfiles.extend R)) ≤
        C * Real.sqrt (radialArea (ContinuousProfiles.extend R))) :
    q ≤ C * Real.sqrt D.area := by
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  let R : ℕ → ContinuousProfiles.Profile := fun n => supportingRadialProfile D hzero (δ n) (hδ n)
  have hR (n : ℕ) : ∀ θ, 0 < R n θ := supportingRadialProfile_pos D hzero (hδ n)
  have harea : Tendsto (fun n => radialArea (ContinuousProfiles.extend (R n))) atTop (𝓝 D.area) :=
    radialArea_supportingRadialProfile_tendsto D hzero hhalf δ hδ
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n => C * Real.sqrt (radialArea (ContinuousProfiles.extend (R n))))
      atTop (𝓝 (C * Real.sqrt D.area)) := tendsto_const_nhds.mul harea.sqrt
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [] with n
  have hm := ContinuousProfiles.domain_isMarked (hR n)
  exact (hq.le_of_weakTorsion_subset_marked hu huc D.isOpen D.bounded hhalf hm
    (subset_radialDomain_supportingRadialProfile D hzero hhalf (hδ n))
    (torsionFlux_spec hm) hline).trans (hbound (R n) (hR n))

end Torsion

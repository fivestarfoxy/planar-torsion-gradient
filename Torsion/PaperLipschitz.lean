module

public import Torsion.CanonicalOptimization
public import Torsion.CanonicalRadialStability

@[expose] public section

/-! # Sharp global Lipschitz and boundary-distance estimates for convex torsion -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion
open Spectral

/-- The area-scaled spectral coefficient as a nonnegative Lipschitz constant. -/
def torsionLipschitzBound (D : ConvexDomain) : ℝ≥0 :=
  ⟨spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt D.area,
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)⟩

private theorem le_lipschitz_mul_infDist_frontier {D : ConvexDomain}
    {U : Plane → ℝ} {L : ℝ≥0} (hL : LipschitzWith L U)
    (hz : ∀ x ∉ D.carrier, U x = 0) {x : Plane} (hx : x ∈ D.carrier) :
    U x ≤ L * infDist x (frontier D.carrier) := by
  obtain ⟨q, hq, _⟩ := D.exists_nearest_supported_frontier hx
  obtain ⟨p, hp, hd⟩ := isClosed_frontier.exists_infDist_eq_dist
    (show (frontier D.carrier).Nonempty from ⟨q, hq⟩) x
  rw [D.isOpen.frontier_eq] at hp
  have hpout : p ∉ D.carrier := hp.2
  calc
    U x ≤ |U x| := le_abs_self _
    _ = dist (U x) (U p) := by rw [hz p hpout, Real.dist_eq, sub_zero]
    _ ≤ L * dist x p := hL.dist_le_mul x p
    _ = L * infDist x (frontier D.carrier) := by rw [hd]

/-- On every bounded nonempty open convex domain the weak torsion function has a
globally Lipschitz zero extension with the sharp spectral coefficient. Its value
is bounded by the same coefficient times the distance to the actual boundary. -/
theorem IsWeakTorsion.exists_sharp_lipschitz_representative
    {D : ConvexDomain} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D.carrier u g) :
    ∃ U : Plane → ℝ, LipschitzWith (torsionLipschitzBound D) U ∧
      (∀ x ∉ D.carrier, U x = 0) ∧ (∀ x, 0 ≤ U x) ∧
      (u =ᵐ[volume.restrict D.carrier] U) ∧
      (∀ x ∈ D.carrier, U x ≤
        spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt D.area *
          infDist x (frontier D.carrier)) := by
  obtain ⟨U, hc, hs, hz, hp, hrep, hg⟩ := hu.exists_continuous_smooth_representative
  have hL : LipschitzWith (torsionLipschitzBound D) U :=
    hu.lipschitzWith_of_boundary_collar_approx D.isOpen D.bounded hc hs hg hz hp
      (fun ε hε => hu.second_boundary_collar hc hrep hz hε)
  exact ⟨U, hL, hz, hp, hrep, fun _ hx => le_lipschitz_mul_infDist_frontier hL hz hx⟩

private theorem markedFlux_of_continuous_weakTorsion
    {D : ConvexDomain} (hm : IsMarked D.carrier) {U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D.carrier U g) (hc : Continuous U) :
    HasMarkedFlux U (torsionFlux D.carrier) := by
  obtain ⟨v, h, r, hv, hr, hvc, hvq⟩ := torsionFlux_spec hm
  have hopen : IsOpen (upperHalfPlane ∩ ball (0 : Plane) r) :=
    (isOpen_lt continuous_const Complex.continuous_im).inter isOpen_ball
  have huv := leOn_open_of_ae_le hopen hc.continuousOn hvc
    (hu.mono hv D.isOpen D.isOpen D.bounded D.bounded Subset.rfl)
  have hvu := leOn_open_of_ae_le hopen hvc hc.continuousOn
    (hv.mono hu D.isOpen D.isOpen D.bounded D.bounded Subset.rfl)
  apply hvq.congr'
  filter_upwards [eventually_vertical_mem_halfBall hr] with t ht
  rw [le_antisymm (hvu _ ht) (huv _ ht)]

/-- Close to a marked origin, the vertical segment has length exactly the
distance to the boundary. Its endpoint at height `t` contains an interior
tangent ball of radius `t` inside the local upper half-ball. -/
theorem IsMarked.eventually_vertical_infDist_frontier {D : Set Plane} (hm : IsMarked D) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (t : ℂ) * Complex.I ∈ D ∧
      infDist ((t : ℂ) * Complex.I) (frontier D) = t := by
  obtain ⟨r, hr, hflat⟩ := hm.2.2.2
  have hsub : upperHalfPlane ∩ ball (0 : Plane) r ⊆ D := by
    rw [← hflat]
    exact inter_subset_left
  have hfront : (0 : Plane) ∈ frontier D := by
    rw [hm.1.frontier_eq]
    refine ⟨closure_mono hsub (origin_mem_closure_halfBall hr), ?_⟩
    intro hzero
    simpa [upperHalfPlane] using hm.2.2.1 hzero
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < r / 2 :=
    (eventually_lt_nhds (half_pos hr)).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_vertical_mem_halfBall hr, self_mem_nhdsWithin, hsmall]
    with t ht ht0 htr
  have htpos : 0 < t := ht0
  let z : Plane := (t : ℂ) * Complex.I
  have hdist : dist z 0 = t := by simp [z, abs_of_pos htpos]
  refine ⟨hsub ht, le_antisymm ((infDist_le_dist_of_mem hfront).trans_eq hdist)
    ((le_infDist ⟨0, hfront⟩).mpr ?_)⟩
  intro y hy
  by_contra! hshort
  change dist z y < t at hshort
  have hym : y ∈ ball (0 : Plane) r := by
    rw [mem_ball]
    have htri := dist_triangle y z 0
    rw [dist_comm y z, hdist] at htri
    linarith
  have hyim : y ∈ upperHalfPlane := by
    have him := Complex.im_le_norm (z - y)
    have hz : z.im = t := by simp [z]
    rw [Complex.sub_im, hz, ← dist_eq_norm] at him
    change 0 < y.im
    linarith
  rw [hm.1.frontier_eq] at hy
  exact hy.2 (hsub ⟨hyim, hym⟩)

/-- The area-one spectral optimizer witnesses sharpness of both estimates.
Every global Lipschitz constant for its zero extension and every coefficient
in its pointwise distance estimate is at least the spectral constant. -/
theorem second_lipschitz_and_distance_sharp :
    ∃ (D : ConvexDomain) (U : Plane → ℝ) (g : Plane → Plane),
      D.carrier = normalizedImage secondEigenvalue secondEigenfunction ∧ D.area = 1 ∧
      IsWeakTorsion D.carrier U g ∧ (∀ x ∉ D.carrier, U x = 0) ∧
      LipschitzWith (torsionLipschitzBound D) U ∧
      HasMarkedFlux U (spectralConstant secondEigenvalue secondEigenfunction) ∧
      (∀ᶠ t : ℝ in 𝓝[>] 0, infDist ((t : ℂ) * Complex.I) (frontier D.carrier) = t) ∧
      (∀ K : ℝ≥0, LipschitzWith K U → spectralConstant secondEigenvalue secondEigenfunction ≤ K) ∧
      (∀ K : ℝ≥0, (∀ x ∈ D.carrier, U x ≤ K * infDist x (frontier D.carrier)) →
        spectralConstant secondEigenvalue secondEigenfunction ≤ K) := by
  obtain ⟨D, hD, hA, _⟩ := second_exact_value.2
  have hu := (torsionTheory.solution D).weakEquation
  obtain ⟨U, hL, hz, _, hrep, _⟩ := hu.exists_sharp_lipschitz_representative
  have hU := hu.of_zero_extension_representative D.isOpen.measurableSet hrep hz
  have hrad : radialDomain (ContinuousProfiles.extend secondAreaOneRadialProfile) =
      D.carrier := secondAreaOneRadialProfile_domain.trans hD.symm
  have hm : IsMarked D.carrier := by
    rw [← hrad]
    exact ContinuousProfiles.domain_isMarked secondAreaOneRadialProfile_pos
  have hq := markedFlux_of_continuous_weakTorsion hm hU hL.continuous
  rw [← hrad, secondAreaOneRadialProfile_flux] at hq
  have hdist := hm.eventually_vertical_infDist_frontier
  have hsharp (K : ℝ≥0) (hK : ∀ x ∈ D.carrier, U x ≤ K * infDist x (frontier D.carrier)) :
      spectralConstant secondEigenvalue secondEigenfunction ≤ K := by
    apply le_of_tendsto_of_tendsto hq tendsto_const_nhds
    filter_upwards [hdist, self_mem_nhdsWithin] with t ht ht0
    have htpos : 0 < t := ht0
    have hh := hK _ ht.1
    rw [ht.2] at hh
    exact (div_le_iff₀ htpos).mpr hh
  exact ⟨D, U, _, hD, hA, hU, hz, hL, hq,
    hdist.mono (fun _ ht => ht.2),
    fun K hK => hsharp K (fun _ hx => le_lipschitz_mul_infDist_frontier hK hz hx), hsharp⟩

end Torsion

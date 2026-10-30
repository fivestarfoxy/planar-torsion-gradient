module

public import Torsion.WeakTranslationLipschitz
public import Torsion.WeakTorsionInterior
public import Torsion.ZeroBoundaryContinuity

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Boundary growth controls the original interior essential gradient norm

The actual weak translation comparison gives a Lipschitz estimate with the
same constant. Local regularity identifies its derivative with the original
weak gradient. Arbitrarily small collar losses disappear in that norm.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal ContDiff

namespace Torsion

/-- A finite nonnegative linear distance bound near the boundary proves
continuity of an actual zero extension. No boundary trace theorem is used. -/
theorem continuous_of_zero_extension_boundary_collar
    {D : Set Plane} (hD : IsOpen D) {U : Plane → ℝ}
    (hU : ContinuousOn U D) (hzero : ∀ x ∉ D, U x = 0)
    (hpos : ∀ x ∈ D, 0 ≤ U x) {L δ : ℝ} (hδ : 0 < δ)
    (hcollar : ∀ x ∈ D, infDist x Dᶜ < δ → U x ≤ L * infDist x Dᶜ) :
    Continuous U := by
  have heq : D.indicator U = U := by
    funext x
    by_cases hx : x ∈ D
    · exact indicator_of_mem hx U
    · rw [indicator_of_notMem hx U, hzero x hx]
  rw [← heq]
  apply continuous_indicator_of_zero_boundary_tendsto hD hU
  intro p hp
  have hpout : p ∈ Dᶜ := by
    rw [hD.frontier_eq] at hp
    exact hp.2
  have hlim : Tendsto (fun x : Plane => L * infDist x Dᶜ) (𝓝[D] p) (𝓝 0) := by
    have hd : Tendsto (fun x : Plane => infDist x Dᶜ) (𝓝[D] p)
        (𝓝 (infDist p Dᶜ)) :=
      ((continuous_infDist_pt Dᶜ).tendsto p).mono_left nhdsWithin_le_nhds
    simpa only [infDist_zero_of_mem hpout, mul_zero] using tendsto_const_nhds.mul hd
  have hsmall : ∀ᶠ x in 𝓝[D] p, infDist x Dᶜ < δ := by
    apply (((continuous_infDist_pt Dᶜ).continuousAt).eventually
      (gt_mem_nhds (by simpa only [infDist_zero_of_mem hpout] using hδ))).filter_mono
        nhdsWithin_le_nhds
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact hpos x hx
  · filter_upwards [self_mem_nhdsWithin, hsmall] with x hx hxs
    exact hcollar x hx hxs

/-- The original essential supremum is bounded by any uniform boundary
distance collar bound for a representative of the actual weak torsion. -/
theorem IsWeakTorsion.gradient_bound_of_boundary_collar
    {D : Set Plane} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : IsOpen D) (hb : Bornology.IsBounded D)
    (hc : Continuous U) (hs : ContDiffOn ℝ ∞ U D)
    (hgrad : g =ᵐ[volume.restrict D] gradient U)
    (hrep : u =ᵐ[volume.restrict D] U)
    (hzero : ∀ x ∉ D, U x = 0) (hpos : ∀ x, 0 ≤ U x)
    {L : ℝ≥0} {δ : ℝ} (hδ : 0 < δ)
    (hcollar : ∀ x ∈ D, infDist x Dᶜ < δ → U x ≤ L * infDist x Dᶜ) :
    eLpNorm g ∞ (volume.restrict D) ≤ (L : ℝ≥0∞) := by
  have hLip := hu.lipschitzWith_of_boundary_collar hD hb hc hs hgrad hzero hpos hδ hcollar
  exact hu.eLpNorm_gradient_le_of_lipschitzOn hD hb hLip.lipschitzOnWith hrep

/-- Arbitrarily small uniform collar losses give the exact bound in the
optimization problem, on the original weak gradient and original domain. -/
theorem IsWeakTorsion.gradient_bound_of_boundary_collar_approx
    {D : Set Plane} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : IsOpen D) (hb : Bornology.IsBounded D)
    (hc : Continuous U) (hs : ContDiffOn ℝ ∞ U D)
    (hgrad : g =ᵐ[volume.restrict D] gradient U)
    (hrep : u =ᵐ[volume.restrict D] U)
    (hzero : ∀ x ∉ D, U x = 0) (hpos : ∀ x, 0 ≤ U x)
    {L : ℝ≥0}
    (hcollar : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ D, infDist x Dᶜ < δ → U x ≤ (L + ε) * infDist x Dᶜ) :
    eLpNorm g ∞ (volume.restrict D) ≤ (L : ℝ≥0∞) := by
  have hLip := hu.lipschitzWith_of_boundary_collar_approx
    hD hb hc hs hgrad hzero hpos hcollar
  exact hu.eLpNorm_gradient_le_of_lipschitzOn hD hb hLip.lipschitzOnWith hrep

end Torsion

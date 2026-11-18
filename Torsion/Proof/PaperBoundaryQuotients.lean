module

public import Torsion.ConvexTorsionContinuity
public import Torsion.BoundaryLowerBound

@[expose] public section

/-! # Normal quotients in arbitrarily thin collars of the original domain -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion

/-- On the closed convex carrier, the continuous torsion representative is
Lipschitz with constant equal to the actual interior weak-gradient norm. -/
theorem DirichletTheory.lipschitzOn_closure_of_gradient (T : DirichletTheory)
    (D : ConvexDomain) {U : Plane → ℝ} (hc : Continuous U)
    (hs : ContDiffOn ℝ ∞ U D.carrier)
    (hg : (T.solution D).weakGradient =ᵐ[volume.restrict D.carrier] gradient U) :
    LipschitzOnWith (T.G D).toNNReal U (closure D.carrier) := by
  apply LipschitzOnWith.closure hc.continuousOn
  apply D.convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    (fun x hx => ((hs.differentiableOn (by simp)) x hx).differentiableAt (D.isOpen.mem_nhds hx))
  intro x hx
  have hcont : ContinuousOn (gradient U) D.carrier :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
      (hs.continuousOn_fderiv_of_isOpen D.isOpen (by simp))
  have hb := enorm_le_eLpNorm_top_on_open D.isOpen hcont hx
  rw [← eLpNorm_congr_ae hg] at hb
  have hreal := ENNReal.toReal_mono (T.G_lt_top D).ne hb
  change ‖fderiv ℝ U x‖ ≤ (T.G D).toReal
  rw [← norm_gradient_eq_fderiv]
  simpa only [toReal_enorm] using hreal

/-- Every strict lower bound for `G(D)` is exceeded by an inward normal
quotient of the original torsion function inside any prescribed boundary collar.
The starting point is a nearest boundary point with a supporting normal, and
the quoted length is exactly the distance to the complement. -/
theorem DirichletTheory.exists_near_maximal_normal_quotients (T : DirichletTheory)
    (D : ConvexDomain) :
    ∃ U : Plane → ℝ, Continuous U ∧ ContDiffOn ℝ ∞ U D.carrier ∧
      (∀ x ∉ D.carrier, U x = 0) ∧ (∀ x, 0 ≤ U x) ∧
      ((T.solution D).value =ᵐ[volume.restrict D.carrier] U) ∧
      ((T.solution D).weakGradient =ᵐ[volume.restrict D.carrier] gradient U) ∧
      LipschitzWith (T.G D).toNNReal U ∧
      ∀ δ : ℝ, 0 < δ → ∀ L : ℝ≥0, (L : ℝ≥0∞) < T.G D →
        ∃ p n : Plane, ∃ t : ℝ, p ∈ frontier D.carrier ∧ ‖n‖ = 1 ∧
          (∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) n (z - p)) ∧ 0 < t ∧ t < δ ∧
          p + t • n ∈ D.carrier ∧ infDist (p + t • n) D.carrierᶜ = t ∧
          (L : ℝ) < U (p + t • n) / t ∧ U (p + t • n) / t ≤ (T.G D).toReal := by
  have hu := (T.solution D).weakEquation
  obtain ⟨U, hc, hs, hz, hp, hrep, hg⟩ := hu.exists_continuous_smooth_representative
  have hLip := T.lipschitzOn_closure_of_gradient D hc hs hg
  have hdist (x : Plane) (hx : x ∈ D.carrier) :
      U x ≤ (T.G D).toReal * infDist x D.carrierᶜ := by
    obtain ⟨p, hf, _, hd, _⟩ := D.exists_nearest_supported_frontier hx
    have hb := hLip.dist_le_mul x (subset_closure hx) p (frontier_subset_closure hf)
    rw [D.isOpen.frontier_eq] at hf
    rwa [Real.dist_eq, hz p hf.2, sub_zero, abs_of_nonneg (hp x), dist_eq_norm, hd] at hb
  have hglobal : LipschitzWith (T.G D).toNNReal U :=
    hu.lipschitzWith_of_boundary_collar D.isOpen D.bounded hc hs hg hz hp
      (by norm_num : (0 : ℝ) < 1) (fun x hx _ => hdist x hx)
  refine ⟨U, hc, hs, hz, hp, hrep, hg, hglobal, ?_⟩
  intro δ hδ L hL
  have hw : ∃ x ∈ D.carrier, infDist x D.carrierᶜ < δ ∧ L * infDist x D.carrierᶜ < U x := by
    by_contra! hno
    exact (not_lt_of_ge (hu.gradient_bound_of_boundary_collar D.isOpen D.bounded
      hc hs hg hrep hz hp hδ hno)) hL
  obtain ⟨x, hx, hthin, hlarge⟩ := hw
  obtain ⟨p, hfront, ht, _, hn, hsupport⟩ := D.exists_nearest_supported_frontier hx
  let t := infDist x D.carrierᶜ
  let n := t⁻¹ • (x - p)
  have hpoint : p + t • n = x := by simp [n, ht.ne', t]
  refine ⟨p, n, t, hfront, hn, hsupport, ht, hthin, ?_⟩
  rw [hpoint]
  refine ⟨hx, rfl, (lt_div_iff₀ ht).mpr hlarge, (div_le_iff₀ ht).mpr ?_⟩
  exact hdist x hx

end Torsion

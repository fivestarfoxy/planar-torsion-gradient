module

public import Torsion.Proof.PaperBrownianTorsion
public import Torsion.Proof.PaperBoundarySlope

@[expose] public section

/-! # The first-order expansion of the actual Brownian mean exit time -/

noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal ENNReal

namespace Torsion.Brownian

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Translation changes the starting point while preserving the local martingale
problem. Pull back the test domains and the test function by the same translation. -/
theorem LocalLaplacianMartingaleProblem.translate {B : ℝ≥0 → Ω → Plane}
    {ℱ : Filtration ℝ≥0 m} (hgen : LocalLaplacianMartingaleProblem B ℱ P) (x : Plane) :
    LocalLaplacianMartingaleProblem (fun t ω => x + B t ω) ℱ P := by
  let e : Plane ≃ₜ Plane := Homeomorph.addLeft x
  intro U V f hU hV hK hVU hf
  have hsub : closure (e ⁻¹' V) ⊆ e ⁻¹' U := by
    rw [← e.preimage_closure]
    exact preimage_mono hVU
  have hK' : IsCompact (closure (e ⁻¹' V)) := by
    rw [← e.preimage_closure]
    exact e.isProperMap.isCompact_preimage hK
  have hs : ContDiffOn ℝ 2 (fun z => f (x + z)) (e ⁻¹' U) :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ h => h)
  have hm := hgen (e ⁻¹' U) (e ⁻¹' V) (fun z => f (x + z))
    (hU.preimage e.continuous) (hV.preimage e.continuous) hK' hsub hs
  have hL (z : Plane) : WeakHarmonicRegularity.planarLaplacian (fun w => f (x + w)) z =
      WeakHarmonicRegularity.planarLaplacian f (x + z) := by
    have hg : gradient (fun w => f (x + w)) = fun w => gradient f (x + w) := by
      funext w
      simp only [gradient, fderiv_comp_add_left]
    simp only [WeakHarmonicRegularity.planarLaplacian, WeakHarmonicRegularity.planarDivergence,
      hg, fderiv_comp_add_left]
  have heq : compensatedTest B (e ⁻¹' V) (fun z => f (x + z)) =
      compensatedTest (fun t ω => x + B t ω) V f := by
    funext t ω
    have ht : cappedExit (e ⁻¹' V) B t ω = cappedExit V (fun s a => x + B s a) t ω := rfl
    simp only [compensatedTest, ht, hL]
  rwa [heq] at hm

/-- For Brownian motion with generator Δ/2, the mean exit time from the open
convex domain equals twice its torsion and has first-order inward coefficient
twice the normal derivative of that same solution. -/
theorem expected_exitTime_boundary_normal_expansion (T : DirichletTheory) (D : ConvexDomain) :
    ∃ U : Plane → ℝ, Continuous U ∧ IsWeakTorsion D.carrier U (T.solution D).weakGradient ∧
      ((T.solution D).value =ᵐ[volume.restrict D.carrier] U) ∧
      ∀ (B : ℝ≥0 → Ω → Plane) (ℱ : Filtration ℝ≥0 m),
        (∀ᵐ ω ∂P, B 0 ω = 0) → (∀ᵐ ω ∂P, Continuous (fun t => B t ω)) →
        LocalLaplacianMartingaleProblem B ℱ P →
        (∀ x : Plane, (∫ ω, (exitTime D.carrier x B ω).toReal ∂P) = 2 * U x) ∧
        ∀ (p n : Plane) (L : Plane →L[ℝ] ℝ), p ∈ frontier D.carrier → ‖n‖ = 1 →
          HasFDerivWithinAt U L (closure D.carrier) p →
          (∀ᶠ t in 𝓝[>] (0 : ℝ), p + t • n ∈ D.carrier) →
          (fun t : ℝ => (∫ ω, (exitTime D.carrier (p + t • n) B ω).toReal ∂P) -
            2 * t * L n) =o[𝓝[>] 0] fun t => t := by
  obtain ⟨U, hc, hu, hz, hrep, hmean⟩ := expected_exitTime_eq_twice_weakTorsion (P := P) T D
  refine ⟨U, hc, hu, hrep, ?_⟩
  intro B ℱ hstart hpaths hgen
  have hm (x : Plane) : (∫ ω, (exitTime D.carrier x B ω).toReal ∂P) = 2 * U x :=
    (hmean x (fun t ω => x + B t ω) ℱ (hstart.mono fun ω h => by simp [h])
      (hpaths.mono fun _ h => continuous_const.add h) (hgen.translate x)).2.2
  refine ⟨hm, ?_⟩
  intro p n L hfront hn hdiff hray
  have hzero := hz p ((D.isOpen.frontier_eq ▸ hfront).2)
  simp_rw [hm]
  exact twice_boundary_normal_expansion hdiff hzero hn hray

end Torsion.Brownian

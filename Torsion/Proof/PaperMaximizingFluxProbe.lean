module

public import Torsion.Proof.PaperWeakFluxBlowup
public import Torsion.Proof.PaperHalfPlaneBumpFlux
public import Torsion.Proof.PaperBoundaryBlowup
public import Torsion.Proof.PaperBoundaryBump
public import Torsion.Proof.PaperHarmonicData

@[expose] public section

/-! # The volume limit for boundary probes at an attaining normal -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion.MaximizingNormalSequence
open HermiteHadamard WeakHarmonicRegularity
variable {T : DirichletTheory} {D : ConvexDomain}

/-- The volume response of the original weak solution recovers the maximizing
normal slope multiplied by the exact integral of the profile on the tangent line. -/
theorem weakBoundaryFlux_bump_tendsto_line (s : MaximizingNormalSequence T D)
    {b : Plane → ℝ} (hb : IsTest univ b) :
    Tendsto (fun ε : ℝ => weakBoundaryFlux D (T.solution D).weakGradient (boundaryBump b s.point ε) / ε)
      (𝓝[>] 0) (𝓝 ((T.G D).toReal * ∫ t : ℝ, b (t • (Complex.I * s.normal)))) := by
  have h := weakBoundaryFlux_bump_tendsto D s.weak.1 s.continuous hb s.point s.normal
    (T.G D).toReal s.blowup_tendsto s.blowup_abs_le
  simpa only [mul_assoc, integral_const_mul, halfPlaneRamp_integral_laplacian s.normal s.unit hb] using h

private theorem raw_isTest : IsTest univ (radialKernelRaw 1) :=
  ⟨radialKernelRaw_contDiff _, radialKernelRaw_hasCompactSupport (by norm_num), subset_univ _⟩

/-- The common radial probe has exactly the coefficient used in the independent
frontier arclength limit. -/
theorem weakBoundaryFlux_profile_tendsto (s : MaximizingNormalSequence T D) :
    Tendsto (fun ε : ℝ => weakBoundaryFlux D (T.solution D).weakGradient
      (boundaryBump (radialKernelRaw 1) s.point ε) / ε) (𝓝[>] 0)
      (𝓝 ((T.G D).toReal * (2 * ∫ t in Ioi (0 : ℝ), boundaryBumpProfile t))) := by
  have hn : ‖Complex.I * s.normal‖ = 1 := by simp [s.unit]
  rw [← boundaryBumpProfile_line hn]
  exact s.weakBoundaryFlux_bump_tendsto_line raw_isTest

/-- Nonnegative classical harmonic functions realizing the scaled volume limit,
with their exact boundary values on the entire complement of the original domain. -/
theorem exists_harmonic_profile_probes (s : MaximizingNormalSequence T D) :
    ∃ H : ℝ → Plane → ℝ,
      (∀ ε > 0, Continuous (H ε) ∧ ContDiffOn ℝ ∞ (H ε) D.carrier ∧
        (∀ z ∈ D.carrier, planarLaplacian (H ε) z = 0) ∧ (∀ z, 0 ≤ H ε z) ∧
        (∀ z ∉ D.carrier, H ε z = boundaryBump (radialKernelRaw 1) s.point ε z)) ∧
      Tendsto (fun ε : ℝ => (∫ z in D.carrier, H ε z) / ε) (𝓝[>] 0)
        (𝓝 ((T.G D).toReal * (2 * ∫ t in Ioi (0 : ℝ), boundaryBumpProfile t))) := by
  classical
  have hex (ε : ℝ) (hε : 0 < ε) := exists_nonneg_harmonic_extension_with_integral D
    (boundaryBump_isTest raw_isTest s.point hε) (fun z => radialKernelRaw_nonneg _ _)
  choose u hc hs hl hz hp he using hex
  let H (ε : ℝ) := if h : 0 < ε then u ε h else 0
  refine ⟨H, ?_, s.weakBoundaryFlux_profile_tendsto.congr' ?_⟩
  · intro ε hε
    simp only [H, dite_eq_left hε]
    exact ⟨hc ε hε, hs ε hε, hl ε hε, hp ε hε, hz ε hε⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    rw [show H ε = u ε hε' from dite_eq_left hε', he ε hε' s.weak]
    rfl

end Torsion.MaximizingNormalSequence

module

public import Torsion.ConvexTorsionContinuity
public import Torsion.ClassicalWeakLaplacian
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

@[expose] public section

/-! # The pointwise Poisson equation for the actual smooth torsion representative -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Torsion

/-- For a smooth interior representative, the original weak torsion equation holds pointwise. -/
theorem IsWeakTorsion.planarLaplacian_representative {D : Set Plane}
    {u U : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g)
    (ho : IsOpen D) (hs : ContDiffOn ℝ ∞ U D)
    (hg : g =ᵐ[volume.restrict D] gradient U) :
    ∀ z ∈ D, WeakHarmonicRegularity.planarLaplacian U z = -1 := by
  let L := WeakHarmonicRegularity.planarLaplacian U
  have hder := (contDiffOn_gradient_of_isOpen hs ho).continuousOn_fderiv_of_isOpen ho (by simp)
  have hc : ContinuousOn L D := by
    apply ContinuousOn.add
    · exact Complex.continuous_re.comp_continuousOn
        ((ContinuousLinearMap.apply ℝ Plane (1 : Plane)).continuous.comp_continuousOn hder)
    · exact Complex.continuous_im.comp_continuousOn
        ((ContinuousLinearMap.apply ℝ Plane Complex.I).continuous.comp_continuousOn hder)
  let F (x : Plane) := L x + 1
  have hF : ContinuousOn F D := hc.add continuousOn_const
  have hAE : ∀ᵐ z ∂volume, z ∈ D → F z = 0 := by
    apply ho.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hF.locallyIntegrableOn ho.measurableSet)
    intro ψ hψ hK hsub
    have ht : IsTest D ψ := ⟨hψ, hK, hsub⟩
    have hprod : Integrable (fun x => L x * ψ x) volume := by
      apply (integrableOn_iff_integrable_of_support_subset (s := tsupport ψ) ?_).mp
      · exact (((hc.mul hψ.continuous.continuousOn).mono hsub).integrableOn_compact hK)
      · intro x hx
        apply subset_tsupport ψ
        exact right_ne_zero_of_mul (show L x * ψ x ≠ 0 from hx)
    have he := hu.representative_smooth_test_equation ho.measurableSet hg ht
    rw [classical_laplacian_smooth_test_equation ho hs ht] at he
    have eqn (x : Plane) : ψ x • F x = L x * ψ x + ψ x := by
      dsimp [F]; ring
    simp_rw [eqn]
    rw [integral_add hprod (hψ.continuous.integrable_of_hasCompactSupport hK)]
    change -(∫ x, L x * ψ x) = ∫ x, ψ x at he
    linarith
  have hEq : EqOn F (fun _ => 0) D := Measure.eqOn_open_of_ae_eq
    ((ae_restrict_iff' ho.measurableSet).2 hAE) ho hF continuousOn_const
  intro z hz
  have h := hEq hz
  change L z + 1 = 0 at h
  change L z = -1
  linarith

end Torsion

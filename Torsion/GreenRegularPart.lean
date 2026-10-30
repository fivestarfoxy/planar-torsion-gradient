module

public import Torsion.ClassicalWeakLaplacian
public import Torsion.HalfPlaneGreenSourceTranslation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A normalized logarithmic pole plus an actual harmonic regular part

This local decomposition proves the exact weak source over the original
compact smooth tests. No conformal transformation of tests or assumed Green
representation is used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion

private theorem gradient_eq_fundamental_add_regular {D : Set Plane}
    {H h : Plane → ℝ} {w x : Plane}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hdecomp : ∀ y ∈ D, y ≠ w → H y = HalfPlane.fundamental w y + h y)
    (hx : x ∈ D) (hp : x ≠ w) :
    gradient H x = gradient (HalfPlane.fundamental w) x + gradient h x := by
  have heq : H =ᶠ[𝓝 x] (fun y => HalfPlane.fundamental w y + h y) := by
    filter_upwards [hD.mem_nhds hx, isOpen_compl_singleton.mem_nhds hp] with y hy hyp
    exact hdecomp y hy hyp
  rw [heq.gradient_eq]
  have hd := ((hh x hx).contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
  simp only [gradient, fderiv_add (HalfPlane.fundamental_hasGradientAt hp).differentiableAt hd,
    map_add]

/-- Every actual logarithmic-pole decomposition with a smooth harmonic
regular part has a genuinely integrable compact-test pairing and the exact
mass-one weak source. All equality hypotheses concern the original scalar
functions on the actual punctured domain. -/
theorem green_regular_part_weak_source {D : Set Plane} {H h ψ : Plane → ℝ} {w : Plane}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hlap : ∀ x ∈ D, WeakHarmonicRegularity.planarLaplacian h x = 0)
    (hdecomp : ∀ x ∈ D, x ≠ w → H x = HalfPlane.fundamental w x + h x)
    (hψ : IsTest D ψ) :
    Integrable (fun x => inner (𝕜 := ℝ) (gradient H x) (gradient ψ x)) ∧
      (∫ x in D, inner (𝕜 := ℝ) (gradient H x) (gradient ψ x)) = ψ w := by
  have hΓ := HalfPlane.fundamental_pairing_integrable_at hψ w
  have hI := classical_smooth_test_pairing_integrable hD hh hψ
  have heq : (fun x => inner (𝕜 := ℝ) (gradient H x) (gradient ψ x)) =ᵐ[volume]
      (fun x => inner (𝕜 := ℝ) (gradient (HalfPlane.fundamental w) x) (gradient ψ x) +
        inner (𝕜 := ℝ) (gradient h x) (gradient ψ x)) := by
    filter_upwards [(countable_singleton w).ae_not_mem volume] with x hp
    have hp : x ≠ w := by simpa using hp
    by_cases hx : x ∈ D
    · rw [gradient_eq_fundamental_add_regular hD hh hdecomp hx hp, inner_add_left]
    · rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hx (hψ.2.2 h))]
      simp
  refine ⟨(hΓ.add hI).congr heq.symm, ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_congr_ae heq, integral_add hΓ hI,
      HalfPlane.fundamental_weak_source_at hψ w,
      classical_harmonic_smooth_test_equation hD hh hlap hψ, add_zero]
  · intro x hx
    rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hx (hψ.2.2 h)), inner_zero_right]

end Torsion

module

public import Torsion.SignedBoundaryAdmission
public import Torsion.ClassicalWeakLaplacian
public import Torsion.SobolevEnergy

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Genuine harmonic uniqueness from signed zero-boundary data -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion

/-- Energy testing gives uniqueness for the original H¹₀ graph on every
bounded open domain, without regularity of its boundary. -/
theorem IsWeakHarmonicOn.value_ae_zero_of_memH10 {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hw : IsWeakHarmonicOn D u g)
    (hu : MemH10 D u g) (hb : Bornology.IsBounded D) : u =ᵐ[volume] 0 := by
  have he := hw.sobolev_test_equation hu.2.1 hu
  simp only [real_inner_self_eq_norm_sq] at he
  exact hu.value_ae_zero_of_gradient_ae_zero hb
    (hu.gradient_ae_zero_of_energy_eq_zero he)

/-- Smooth signed harmonic data with continuous zero extension and finite
actual energy vanish. Signed boundary admission and energy uniqueness are
proved, rather than supplied as a trace or representation hypothesis. -/
theorem classical_harmonic_eq_zero_of_zero_extension {D : Set Plane}
    (hD : IsOpen D) (hb : Bornology.IsBounded D)
    {u : Plane → ℝ} {g : Plane → Plane}
    (hc : Continuous u) (hs : ContDiffOn ℝ ∞ u D)
    (hzero : ∀ x ∉ D, u x = 0)
    (hgrad : ∀ x ∈ D, g x = gradient u x) (hgzero : ∀ x ∉ D, g x = 0)
    (huLp : MemLp u 2 volume) (hgLp : MemLp g 2 volume)
    (hlap : ∀ x ∈ D, WeakHarmonicRegularity.planarLaplacian u x = 0) :
    ∀ x, u x = 0 := by
  have hu := BoundaryAdmission.memH10_of_smooth_zero_extension hD hb hc hs
    hzero hgrad hgzero huLp hgLp
  have hw : IsWeakHarmonicOn D u g := by
    refine ⟨hu.distributionalGradient, ?_⟩
    intro ψ hψ
    have heq : (fun x => inner (𝕜 := ℝ) (g x) (gradient ψ x)) =
        (fun x => inner (𝕜 := ℝ) (gradient u x) (gradient ψ x)) := by
      funext x
      by_cases hx : x ∈ D
      · rw [hgrad x hx]
      · simp [gradient_eq_zero_of_not_mem_tsupport (fun h => hx (hψ.2.2 h))]
    rw [heq]
    exact classical_harmonic_smooth_test_equation hD hs hlap hψ
  have hae := hw.value_ae_zero_of_memH10 hu hb
  have hpoint := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae)
    isOpen_univ hc.continuousOn continuousOn_const
  intro x
  exact hpoint (mem_univ x)

end Torsion

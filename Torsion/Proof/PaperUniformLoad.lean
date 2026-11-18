module

public import Torsion.SobolevScalar
public import Torsion.CanonicalOptimization
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

@[expose] public section

/-! # Scaling the torsion solution to a membrane under uniform transverse load -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Torsion

/-- The displacement and weak gradient scale by load divided by tension.
The test identity here has the physical forcing on the right. -/
theorem IsWeakTorsion.uniform_membrane_load {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g)
    (p τ : ℝ) (hτ : 0 < τ) :
    MemH10 D (fun x => (p/τ) • u x) (fun x => (p/τ) • g x) ∧
      ∀ (v : Plane → ℝ) (h : Plane → Plane), MemH10 D v h →
        τ * (∫ x in D, inner (𝕜 := ℝ) ((p/τ) • g x) (h x)) = p * ∫ x in D, v x := by
  refine ⟨hu.1.const_smul _, ?_⟩
  intro v h hv
  simp only [real_inner_smul_left, integral_const_mul, hu.2 v h hv]
  field_simp

/-- The physical peak slope is the load-to-tension ratio times the
normalized torsion gradient. -/
theorem DirichletTheory.uniform_membrane_peak (T : DirichletTheory) (D : ConvexDomain)
    {p τ : ℝ} (hp : 0 < p) (hτ : 0 < τ) :
    eLpNorm (fun x => (p/τ) • (T.solution D).weakGradient x) ∞ (volume.restrict D.carrier) =
      ENNReal.ofReal (p/τ) * T.G D := by
  change eLpNorm ((p/τ) • (T.solution D).weakGradient) _ _ = _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (div_pos hp hτ).le]
  rfl

/-- Tests supported in the interior have zero boundary flux, by the weak
Poisson equation. -/
theorem IsWeakTorsion.interior_test_boundary_flux_zero {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g)
    {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    (∫ z in D, ψ z) - (∫ z in D, inner (𝕜 := ℝ) (g z) (gradient ψ z)) = 0 := by
  rw [hu.2 ψ (gradient ψ) hψ.memH10, sub_self]

/-- The zero-extended weak equation defines the outward flux, tested
against boundary values extended by ψ into the domain. For a test equal
to one near the domain, total outward flux equals its area. -/
theorem unit_load_total_flux (D : ConvexDomain) (g : Plane → Plane) {ψ : Plane → ℝ}
    (hψ : ∀ z ∈ D.carrier, ψ =ᶠ[nhds z] fun _ => (1 : ℝ)) :
    (∫ z in D.carrier, ψ z) -
      (∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (gradient ψ z)) = D.area := by
  have hconst : (∫ z in D.carrier, ψ z) = ∫ _ in D.carrier, (1 : ℝ) :=
    setIntegral_congr_fun D.isOpen.measurableSet (fun z hz => (hψ z hz).self_of_nhds)
  have hzero : (∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (gradient ψ z)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with z hz
    have hg : gradient ψ z = 0 := by
      unfold gradient
      rw [(hψ z hz).fderiv_eq]
      simp
    simp only [hg, inner_zero_right, Pi.zero_apply]
  rw [hconst, hzero, sub_zero, setIntegral_const]
  simp [ConvexDomain.area, Measure.real_def]

end Torsion

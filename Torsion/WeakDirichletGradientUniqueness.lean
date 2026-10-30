import Torsion.MarkedFluxFixedKernel

/-! # Gradient uniqueness from actual compact-test Dirichlet equations -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Two actual zero-boundary H¹ pairs with the same compact-test energy
equation have identical weak gradients. Density in the original graph
makes their difference an admissible test; no boundary trace assertion or
extra uniqueness certificate is required. -/
theorem MemH10.gradient_ae_eq_of_smooth_test_equation
    {D : Set Plane} {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : MemH10 D u g) (hv : MemH10 D v h)
    (htest : ∀ ψ : Plane → ℝ, IsTest D ψ →
      (∫ z, inner (𝕜 := ℝ) (g z) (gradient ψ z)) =
        ∫ z, inner (𝕜 := ℝ) (h z) (gradient ψ z)) :
    g =ᵐ[volume] h := by
  have hdiff := hu.sub hv
  have hw : IsWeakHarmonicOn D (fun z => u z - v z) (fun z => g z - h z) := by
    refine ⟨hdiff.distributionalGradient, ?_⟩
    intro ψ hψ
    simp only [inner_sub_left]
    rw [integral_sub
      (integrable_real_inner_of_memLp_two hu.2.1 (hψ.memLp_gradient (p := 2)))
      (integrable_real_inner_of_memLp_two hv.2.1 (hψ.memLp_gradient (p := 2))),
      htest ψ hψ, sub_self]
  have henergy := hw.sobolev_test_equation hdiff.2.1 hdiff
  have hnormenergy : (∫ z, ‖g z - h z‖ ^ 2) = 0 := by
    simpa only [real_inner_self_eq_norm_sq] using henergy
  have hnormint : Integrable (fun z => ‖g z - h z‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hdiff.2.1.1).mp hdiff.2.1
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun z => sq_nonneg ‖g z - h z‖) hnormint).mp hnormenergy
  filter_upwards [hae] with z hz
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- The fixed marked derivative agrees for such genuine Dirichlet pairs,
independently of all weak-gradient representative choices. -/
theorem markedGradientFlux_eq_of_smooth_test_equation
    {D : Set Plane} {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : MemH10 D u g) (hv : MemH10 D v h)
    (htest : ∀ ψ : Plane → ℝ, IsTest D ψ →
      (∫ z, inner (𝕜 := ℝ) (g z) (gradient ψ z)) =
        ∫ z, inner (𝕜 := ℝ) (h z) (gradient ψ z)) (r : ℝ) :
    markedGradientFlux r g = markedGradientFlux r h :=
  markedGradientFlux_congr_ae (hu.gradient_ae_eq_of_smooth_test_equation hv htest) r

end Torsion

module

public import Torsion.ShapeSobolevDeformation

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The genuine weak torsion equation under a smooth domain change

The original test graph is pushed to the physical image through the actual
smooth inverse. The original weak equation and the pinned Jacobian
change-of-variables theorem give its fixed-domain form for every genuine
H¹₀ test. The common small parameter interval and two-way graph transport
are constructed from the actual smooth compact vector field. Differentiability
of the family of solutions remains a subsequent variational argument.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

namespace Torsion.Shape

/-- The genuine fixed-domain energy operator `J DT⁻¹ DT⁻ᵀ`, written using
the derivative of the actual inverse map at the physical image point. -/
def pullbackEnergyOperator (e : Plane ≃ₜ Plane) (z : Plane) : Plane →L[ℝ] Plane :=
  (fderiv ℝ (e : Plane → Plane) z).det •
    (fderiv ℝ (e.symm : Plane → Plane) (e z)).comp
      (fderiv ℝ (e.symm : Plane → Plane) (e z)).adjoint

theorem pullbackEnergyOperator_apply_inner (e : Plane ≃ₜ Plane) (z p q : Plane) :
    inner (𝕜 := ℝ) (pullbackEnergyOperator e z p) q =
      (fderiv ℝ (e : Plane → Plane) z).det *
        inner (𝕜 := ℝ) ((fderiv ℝ (e.symm : Plane → Plane) (e z)).adjoint p)
          ((fderiv ℝ (e.symm : Plane → Plane) (e z)).adjoint q) := by
  simp only [pullbackEnergyOperator, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, real_inner_smul_left]
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- Pushforward of the actual compact smooth test core by a smooth inverse. -/
theorem test_pushforward {D : Set Plane} {f : Plane → ℝ} (e : Plane ≃ₜ Plane)
    (heinv : ContDiff ℝ ∞ (e.symm : Plane → Plane)) (hf : IsTest D f) :
    IsTest (e '' D) (f ∘ e.symm) := by
  have hD : e.symm '' (e '' D) = D := e.symm_image_image D
  exact test_pullback e.symm heinv (hD.symm ▸ hf)

/-- The exact fixed-domain equation follows from the original weak torsion
equation. Its coefficient uses the actual inverse differential and physical
Jacobian. No transport identity is assumed. -/
theorem weakTorsion_compact_test_pullback {D : Set Plane} {u : Plane → ℝ}
    {g : Plane → Plane} (e : Plane ≃ₜ Plane)
    (he : ContDiff ℝ ∞ (e : Plane → Plane))
    (heinv : ContDiff ℝ ∞ (e.symm : Plane → Plane)) (hD : MeasurableSet D)
    (hu : IsWeakTorsion (e '' D) u g) {f : Plane → ℝ} (hf : IsTest D f) :
    (∫ z in D, |(fderiv ℝ (e : Plane → Plane) z).det| *
      inner (𝕜 := ℝ) (g (e z)) (gradientPullback e.symm (gradient f) (e z))) =
    ∫ z in D, |(fderiv ℝ (e : Plane → Plane) z).det| * f z := by
  have htest := test_pushforward e heinv hf
  have hw := hu.2 (f ∘ e.symm) (gradient (f ∘ e.symm)) htest.memH10
  have heD (z : Plane) (_hz : z ∈ D) :
      HasFDerivWithinAt e (fderiv ℝ (e : Plane → Plane) z) D z :=
    ((he.differentiable (by simp)) z).hasFDerivAt.hasFDerivWithinAt
  have hl := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hD heD
    e.injective.injOn (fun w => inner (𝕜 := ℝ) (g w) (gradient (f ∘ e.symm) w))
  have hr := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hD heD
    e.injective.injOn (f ∘ e.symm)
  rw [hl, hr] at hw
  have hgrad : gradient (f ∘ e.symm) = gradientPullback e.symm (gradient f) := by
    funext w
    exact gradient_comp ((heinv.differentiable (by simp)) w)
      ((hf.1.differentiable (by simp)) (e.symm w))
  simpa only [hgrad, smul_eq_mul, Function.comp_apply, e.symm_apply_apply] using hw

/-- If the deformation preserves orientation, its signed Jacobian is the
density in the true fixed-domain weak equation. -/
theorem weakTorsion_compact_test_pullback_of_det_nonneg {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (e : Plane ≃ₜ Plane)
    (he : ContDiff ℝ ∞ (e : Plane → Plane))
    (heinv : ContDiff ℝ ∞ (e.symm : Plane → Plane)) (hD : MeasurableSet D)
    (hJ : ∀ z ∈ D, 0 ≤ (fderiv ℝ (e : Plane → Plane) z).det)
    (hu : IsWeakTorsion (e '' D) u g) {f : Plane → ℝ} (hf : IsTest D f) :
    (∫ z in D, (fderiv ℝ (e : Plane → Plane) z).det *
      inner (𝕜 := ℝ) (g (e z)) (gradientPullback e.symm (gradient f) (e z))) =
    ∫ z in D, (fderiv ℝ (e : Plane → Plane) z).det * f z := by
  have hw := weakTorsion_compact_test_pullback e he heinv hD hu hf
  have hl : (∫ z in D, |(fderiv ℝ (e : Plane → Plane) z).det| *
      inner (𝕜 := ℝ) (g (e z)) (gradientPullback e.symm (gradient f) (e z))) =
      ∫ z in D, (fderiv ℝ (e : Plane → Plane) z).det *
        inner (𝕜 := ℝ) (g (e z)) (gradientPullback e.symm (gradient f) (e z)) := by
    apply setIntegral_congr_fun hD
    intro z hz
    dsimp only
    rw [abs_of_nonneg (hJ z hz)]
  have hr : (∫ z in D, |(fderiv ℝ (e : Plane → Plane) z).det| * f z) =
      ∫ z in D, (fderiv ℝ (e : Plane → Plane) z).det * f z := by
    apply setIntegral_congr_fun hD
    intro z hz
    dsimp only
    rw [abs_of_nonneg (hJ z hz)]
  rwa [hl, hr] at hw

/-- A transported genuine H¹₀ test gives the exact transformed weak equation,
including its original weak-gradient representative. -/
theorem weakTorsion_pullback_test {D : Set Plane} {u v : Plane → ℝ}
    {g h : Plane → Plane} (e : Plane ≃ₜ Plane)
    (he : ContDiff ℝ ∞ (e : Plane → Plane))
    (heinv : ContDiff ℝ ∞ (e.symm : Plane → Plane)) (hD : MeasurableSet D)
    (hu : IsWeakTorsion (e '' D) u g)
    (hv : MemH10 (e '' D) (v ∘ e.symm) (gradientPullback e.symm h)) :
    (∫ z in D, |(fderiv ℝ (e : Plane → Plane) z).det| *
      inner (𝕜 := ℝ)
        ((fderiv ℝ (e.symm : Plane → Plane) (e z)).adjoint (gradientPullback e g z))
        ((fderiv ℝ (e.symm : Plane → Plane) (e z)).adjoint (h z))) =
    ∫ z in D, |(fderiv ℝ (e : Plane → Plane) z).det| * v z := by
  have hw := hu.2 (v ∘ e.symm) (gradientPullback e.symm h) hv
  have heD (z : Plane) (_hz : z ∈ D) :
      HasFDerivWithinAt e (fderiv ℝ (e : Plane → Plane) z) D z :=
    ((he.differentiable (by simp)) z).hasFDerivAt.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hD heD e.injective.injOn,
    integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hD heD e.injective.injOn] at hw
  have hcancel (z : Plane) : g (e z) =
      (fderiv ℝ (e.symm : Plane → Plane) (e z)).adjoint (gradientPullback e g z) := by
    have hc := gradientPullback_inverse_cancel e (he.differentiable (by simp))
      (heinv.differentiable (by simp)) g (e z)
    simpa only [gradientPullback, e.symm_apply_apply] using hc.symm
  simp only [smul_eq_mul, Function.comp_apply, e.symm_apply_apply] at hw
  calc
    _ = ∫ z in D, |(fderiv ℝ (e : Plane → Plane) z).det| *
        inner (𝕜 := ℝ) (g (e z)) (gradientPullback e.symm h (e z)) := by
      apply setIntegral_congr_fun hD
      intro z _
      dsimp only
      rw [hcancel z]
      simp only [gradientPullback, e.symm_apply_apply]
    _ = _ := hw

/-- The true fixed-domain variational equation holds for every original H¹₀
test under every sufficiently small actual smooth compact deformation.
The map, smooth inverse, graph transport and Jacobian positivity are all
constructed internally from `V`; they are not extra analytic hypotheses. -/
theorem exists_weakTorsion_pullback_deformation {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      ∃ e : Plane ≃ₜ Plane, (e : Plane → Plane) = deformation V t ∧
        ContDiff ℝ ∞ (e.symm : Plane → Plane) ∧
        ∀ (D : Set Plane), MeasurableSet D → ∀ (u : Plane → ℝ) (g : Plane → Plane),
          IsWeakTorsion (deformation V t '' D) u g →
          MemH10 D (u ∘ e) (gradientPullback e g) ∧
          ∀ (v : Plane → ℝ) (h : Plane → Plane), MemH10 D v h →
            (∫ z in D, inner (𝕜 := ℝ)
              (pullbackEnergyOperator e z (gradientPullback e g z)) (h z)) =
            ∫ z in D, (fderiv ℝ (e : Plane → Plane) z).det * v z := by
  obtain ⟨δ₀, hδ₀, htransport⟩ := exists_MemH10_transport_deformation hV hVc
  obtain ⟨δJ, hδJ, hJ⟩ := exists_uniform_jacobian_half_le hV hVc
  refine ⟨min δ₀ δJ, lt_min hδ₀ hδJ, ?_⟩
  intro t ht
  obtain ⟨e, heq, heinv, hpull, hpush⟩ := htransport t (ht.trans_le (min_le_left _ _))
  have he : ContDiff ℝ ∞ (e : Plane → Plane) := by
    rw [heq]
    exact deformation_contDiff hV t
  refine ⟨e, heq, heinv, ?_⟩
  intro D hD u g hu
  refine ⟨hpull D u g hu.1, ?_⟩
  intro v h hv
  have hu' : IsWeakTorsion (e '' D) u g := by simpa only [heq] using hu
  have hv' : MemH10 (e '' D) (v ∘ e.symm) (gradientPullback e.symm h) := by
    simpa only [heq] using hpush D v h hv
  have hw := weakTorsion_pullback_test e he heinv hD hu' hv'
  have habs (z : Plane) : |(fderiv ℝ (e : Plane → Plane) z).det| =
      (fderiv ℝ (e : Plane → Plane) z).det := by
    apply abs_of_nonneg
    have hj := hJ t (ht.trans_le (min_le_right _ _)) z
    rw [← heq] at hj
    linarith
  simpa only [habs, pullbackEnergyOperator_apply_inner] using hw

end Torsion.Shape

import Torsion.ShapeDeformation
import Torsion.WeakGradient
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The actual gradient pullback under smooth planar deformations -/

noncomputable section
open Set
open scoped Topology ContDiff

namespace Torsion.Shape

/-- Pullback of a physical weak-gradient field by the transpose differential. -/
def gradientPullback (T : Plane → Plane) (g : Plane → Plane) (z : Plane) : Plane :=
  (fderiv ℝ T z).adjoint (g (T z))

/-- The genuine classical chain rule on the compact smooth core. -/
theorem gradient_comp {T : Plane → Plane} {f : Plane → ℝ} {z : Plane}
    (hT : DifferentiableAt ℝ T z) (hf : DifferentiableAt ℝ f (T z)) :
    gradient (f ∘ T) z = gradientPullback T (gradient f) z := by
  apply ext_inner_right ℝ
  intro v
  rw [← fderiv_apply_eq_inner_gradient]
  rw [(hf.hasFDerivAt.comp z hT.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, gradientPullback]
  rw [ContinuousLinearMap.adjoint_inner_left, ← fderiv_apply_eq_inner_gradient]

theorem gradientPullback_sub (T : Plane → Plane) (g h : Plane → Plane) (z : Plane) :
    gradientPullback T (fun w => g w - h w) z =
      gradientPullback T g z - gradientPullback T h z := by
  simp [gradientPullback]

theorem gradientPullback_norm_le (T : Plane → Plane) (g : Plane → Plane) (z : Plane) :
    ‖gradientPullback T g z‖ ≤ ‖fderiv ℝ T z‖ * ‖g (T z)‖ := by
  simpa [gradientPullback] using (fderiv ℝ T z).adjoint.le_opNorm (g (T z))

/-- The gradient of the actual deformed compact test is the pullback field. -/
theorem test_gradient_pullback {D : Set Plane} {f : Plane → ℝ}
    {T : Plane → Plane} (hf : IsTest D f) (hT : ContDiff ℝ ∞ T) :
    gradient (f ∘ T) = gradientPullback T (gradient f) := by
  funext z
  exact gradient_comp ((hT.differentiable (by simp)) z)
    ((hf.1.differentiable (by simp)) (T z))

/-- The two actual transpose differentials cancel under a smooth inverse. -/
theorem gradientPullback_inverse_cancel (e : Plane ≃ₜ Plane)
    (he : Differentiable ℝ (e : Plane → Plane))
    (heinv : Differentiable ℝ (e.symm : Plane → Plane)) (g : Plane → Plane) (w : Plane) :
    gradientPullback e.symm (gradientPullback e g) w = g w := by
  have hd := (he (e.symm w)).hasFDerivAt.comp w (heinv w).hasFDerivAt
  have hcomp : (e : Plane → Plane) ∘ e.symm = id := funext e.apply_symm_apply
  have heq : (fderiv ℝ (e : Plane → Plane) (e.symm w)).comp
      (fderiv ℝ (e.symm : Plane → Plane) w) = ContinuousLinearMap.id ℝ Plane := by
    rw [hcomp] at hd
    exact hd.unique (hasFDerivAt_id w)
  unfold gradientPullback
  rw [e.apply_symm_apply]
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp, heq]
  simp

end Torsion.Shape

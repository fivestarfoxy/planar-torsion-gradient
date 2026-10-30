import Torsion.ShapeWeakPullback
import Torsion.ShapeCoefficients

/-! # Identification of the actual weak pullback coefficient with its matrix -/

noncomputable section
open Set
open scoped Topology ContDiff Matrix

namespace Torsion.Shape

theorem realMatrix_comp (L M : Plane →L[ℝ] Plane) :
    realMatrix (L.comp M) = realMatrix L * realMatrix M := by
  exact LinearMap.toMatrix_comp Complex.basisOneI Complex.basisOneI Complex.basisOneI
    L.toLinearMap M.toLinearMap

theorem realMatrix_smul (a : ℝ) (L : Plane →L[ℝ] Plane) :
    realMatrix (a • L) = a • realMatrix L := by
  exact map_smul (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI) a L.toLinearMap

/-- In the physical orthonormal basis `(1,I)`, adjoint is exactly transpose. -/
theorem realMatrix_adjoint (L : Plane →L[ℝ] Plane) :
    realMatrix L.adjoint = (realMatrix L)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [realMatrix, LinearMap.toMatrix_apply, Complex.coe_basisOneI,
      Complex.coe_basisOneI_repr, Matrix.transpose_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const] <;>
    first
    | simpa [Complex.inner, Complex.mul_re] using L.adjoint_inner_left (1 : Plane) (1 : Plane)
    | simpa [Complex.inner, Complex.mul_re] using L.adjoint_inner_left (1 : Plane) Complex.I
    | simpa [Complex.inner, Complex.mul_re] using L.adjoint_inner_left Complex.I (1 : Plane)
    | simpa [Complex.inner, Complex.mul_re] using L.adjoint_inner_left Complex.I Complex.I

/-- The derivative of the genuine smooth inverse is the matrix inverse of
the forward derivative, with no extra inverse-differential certificate. -/
theorem realMatrix_fderiv_inverse (e : Plane ≃ₜ Plane)
    (he : Differentiable ℝ (e : Plane → Plane))
    (heinv : Differentiable ℝ (e.symm : Plane → Plane)) (z : Plane) :
    realMatrix (fderiv ℝ (e.symm : Plane → Plane) (e z)) =
      (realMatrix (fderiv ℝ (e : Plane → Plane) z))⁻¹ := by
  have hd := (he (e.symm (e z))).hasFDerivAt.comp (e z) (heinv (e z)).hasFDerivAt
  have hcomp : (e : Plane → Plane) ∘ e.symm = id := funext e.apply_symm_apply
  simp only [e.symm_apply_apply] at hd
  rw [hcomp] at hd
  have heq := hd.unique (hasFDerivAt_id (e z))
  apply (Matrix.inv_eq_right_inv ?_).symm
  rw [← realMatrix_comp, heq]
  change LinearMap.toMatrix Complex.basisOneI Complex.basisOneI LinearMap.id = 1
  exact LinearMap.toMatrix_id Complex.basisOneI

/-- The coefficient in the actual pulled-back weak equation is precisely
the physical inverse-Jacobian matrix, including the determinant factor. -/
theorem realMatrix_pullbackEnergyOperator (e : Plane ≃ₜ Plane)
    (he : Differentiable ℝ (e : Plane → Plane))
    (heinv : Differentiable ℝ (e.symm : Plane → Plane)) (z : Plane) :
    realMatrix (pullbackEnergyOperator e z) =
      (fderiv ℝ (e : Plane → Plane) z).det •
        ((realMatrix (fderiv ℝ (e : Plane → Plane) z))⁻¹ *
          ((realMatrix (fderiv ℝ (e : Plane → Plane) z))⁻¹)ᵀ) := by
  unfold pullbackEnergyOperator
  rw [realMatrix_smul, realMatrix_comp, realMatrix_adjoint,
    realMatrix_fderiv_inverse e he heinv z]

/-- Hence the matrix whose first variation was proved is the coefficient
of the genuine weak equation for the actual deformation. -/
theorem realMatrix_pullbackEnergyOperator_deformation {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (t : ℝ) (e : Plane ≃ₜ Plane)
    (heq : (e : Plane → Plane) = deformation V t)
    (heinv : ContDiff ℝ ∞ (e.symm : Plane → Plane)) (z : Plane) :
    realMatrix (pullbackEnergyOperator e z) = physicalEnergyMatrix V t z := by
  have he : ContDiff ℝ ∞ (e : Plane → Plane) := by
    rw [heq]
    exact deformation_contDiff hV t
  rw [realMatrix_pullbackEnergyOperator e (he.differentiable (by simp))
    (heinv.differentiable (by simp)) z, heq]
  rfl

end Torsion.Shape

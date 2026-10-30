module

public import Torsion.ShapeCoefficients
public import Torsion.SobolevCore
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual fixed-domain forcing and its shape derivative

In dimension two the true Jacobian of `id + t V` is an exact quadratic
polynomial. Multiplication by an actual compact smooth test and integration
therefore gives the fixed-domain forcing derivative with no assumed
differentiation-under-the-integral certificate. Compactness of the vector
field itself is unnecessary for this local compact-test calculation.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

namespace Torsion.Shape

/-- The determinant of the actual real coordinate matrix is the coordinate
independent determinant of the original differential. -/
theorem realMatrix_det (L : Plane →L[ℝ] Plane) :
    (realMatrix L).det = L.det :=
  LinearMap.det_toMatrix Complex.basisOneI L.toLinearMap

theorem divergence_continuous {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) :
    Continuous (divergence V) := by
  have hd := hV.continuous_fderiv (by simp)
  exact (Complex.continuous_re.comp (hd.clm_apply continuous_const)).add
    (Complex.continuous_im.comp (hd.clm_apply continuous_const))

/-- Exact integrated Jacobian polynomial for an actual compact test. -/
theorem physical_forcing_polynomial {D : Set Plane} {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) {f : Plane → ℝ} (hf : IsTest D f) (t : ℝ) :
    (∫ z in D, LinearMap.det (fderiv ℝ (deformation V t) z).toLinearMap * f z) =
      (∫ z in D, f z) + t * (∫ z in D, divergence V z * f z) +
        t ^ 2 * (∫ z in D, (fderiv ℝ V z).det * f z) := by
  have hfd := hV.continuous_fderiv (by simp)
  have hid : IntegrableOn (fun z => divergence V z * f z) D :=
    (((divergence_continuous hV).mul hf.1.continuous).integrable_of_hasCompactSupport
      hf.2.1.mul_left).restrict
  have hiJ : IntegrableOn (fun z => (fderiv ℝ V z).det * f z) D :=
    (((ContinuousLinearMap.continuous_det.comp hfd).mul hf.1.continuous).integrable_of_hasCompactSupport
      hf.2.1.mul_left).restrict
  have hif : IntegrableOn f D :=
    (hf.1.continuous.integrable_of_hasCompactSupport hf.2.1).restrict
  calc
    _ = ∫ z in D, f z + t * (divergence V z * f z) +
        t ^ 2 * ((fderiv ℝ V z).det * f z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [det_fderiv_deformation ((hV.differentiable (by simp)) z) t,
        jacobian_polynomial, realMatrix_det, trace_realMatrix]
      dsimp only [divergence]
      ring
    _ = _ := by
      have ha := integral_add (hif.add (hid.const_mul t)) (hiJ.const_mul (t ^ 2))
      simp only [Pi.add_apply] at ha
      rw [ha, integral_add hif (hid.const_mul t), integral_const_mul, integral_const_mul]

/-- The actual fixed-domain forcing is differentiable at every parameter,
with the exact quadratic-Jacobian derivative. -/
theorem physical_forcing_hasDerivAt {D : Set Plane} {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) {f : Plane → ℝ} (hf : IsTest D f) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
      ∫ z in D, LinearMap.det (fderiv ℝ (deformation V s) z).toLinearMap * f z)
      ((∫ z in D, divergence V z * f z) +
        2 * t * (∫ z in D, (fderiv ℝ V z).det * f z)) t := by
  have h := ((hasDerivAt_const t (∫ z in D, f z)).add
    ((hasDerivAt_id t).mul_const (∫ z in D, divergence V z * f z))).add
    (((hasDerivAt_id t).pow 2).mul_const (∫ z in D, (fderiv ℝ V z).det * f z))
  convert h using 1
  · funext s
    exact physical_forcing_polynomial hV hf s
  · simp

/-- The forcing term in the actual fixed-domain weak Dirichlet equation has
first variation `∫ (div V) f`, with the correct normalization. -/
theorem physical_forcing_hasDerivAt_zero {D : Set Plane} {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) {f : Plane → ℝ} (hf : IsTest D f) :
    HasDerivAt (fun t : ℝ =>
      ∫ z in D, LinearMap.det (fderiv ℝ (deformation V t) z).toLinearMap * f z)
      (∫ z in D, divergence V z * f z) 0 := by
  simpa using physical_forcing_hasDerivAt hV hf 0

end Torsion.Shape

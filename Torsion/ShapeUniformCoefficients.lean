import Torsion.ShapeCoefficients
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Uniform first variations of actual compact shape coefficients

The coordinate fields of the true differential of a smooth compact vector
field are constructed in the Banach algebra of bounded continuous functions.
Derivatives in this algebra are derivatives in the global supremum norm.
The Jacobian and inverse-Jacobian coefficients therefore have uniform first
variations, rather than merely pointwise derivatives.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Torsion.Shape

abbrev CoefficientField := BoundedContinuousFunction Plane ℝ

theorem differential_entry_continuous {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (i j : Fin 2) : Continuous (fun z => realMatrix (fderiv ℝ V z) i j) := by
  have hd := hV.continuous_fderiv (by simp)
  fin_cases i <;> fin_cases j <;>
    simp only [realMatrix, LinearMap.toMatrix_apply, Complex.coe_basisOneI,
      Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const] <;>
    first | exact Complex.continuous_re.comp (hd.clm_apply continuous_const)
          | exact Complex.continuous_im.comp (hd.clm_apply continuous_const)

theorem differential_entry_hasCompactSupport {V : Plane → Plane} (hVc : HasCompactSupport V)
    (i j : Fin 2) : HasCompactSupport (fun z => realMatrix (fderiv ℝ V z) i j) := by
  apply hVc.mono'
  intro z hz
  by_contra hnot
  apply hz
  change realMatrix (fderiv ℝ V z) i j = 0
  rw [fderiv_of_not_mem_tsupport ℝ hnot]
  simp [realMatrix]

/-- An actual bounded continuous coordinate field of `DV`. -/
def boundedDifferentialEntry {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (i j : Fin 2) : CoefficientField :=
  ofCompactSupport (fun z => realMatrix (fderiv ℝ V z) i j)
    (differential_entry_continuous hV i j) (differential_entry_hasCompactSupport hVc i j)

@[simp] theorem boundedDifferentialEntry_apply {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (i j : Fin 2) (z : Plane) :
    boundedDifferentialEntry hV hVc i j z = realMatrix (fderiv ℝ V z) i j := rfl

def boundedDivergence {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) : CoefficientField :=
  boundedDifferentialEntry hV hVc 0 0 + boundedDifferentialEntry hV hVc 1 1

def boundedDifferentialDet {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) : CoefficientField :=
  boundedDifferentialEntry hV hVc 0 0 * boundedDifferentialEntry hV hVc 1 1 -
    boundedDifferentialEntry hV hVc 0 1 * boundedDifferentialEntry hV hVc 1 0

@[simp] theorem boundedDivergence_apply {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (z : Plane) : boundedDivergence hV hVc z = divergence V z := by
  simpa [boundedDivergence, Matrix.trace, Fin.sum_univ_two, divergence] using
    trace_realMatrix (fderiv ℝ V z)

@[simp] theorem boundedDifferentialDet_apply {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (z : Plane) :
    boundedDifferentialDet hV hVc z = (realMatrix (fderiv ℝ V z)).det := by
  simp [boundedDifferentialDet, Matrix.det_fin_two]

/-- The true Jacobian as a bounded continuous physical field. -/
def uniformJacobian {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (t : ℝ) : CoefficientField :=
  1 + t • boundedDivergence hV hVc + t ^ 2 • boundedDifferentialDet hV hVc

@[simp] theorem uniformJacobian_zero {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) : uniformJacobian hV hVc 0 = 1 := by simp [uniformJacobian]

theorem uniformJacobian_apply {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (t : ℝ) (z : Plane) :
    uniformJacobian hV hVc t z =
      LinearMap.det (fderiv ℝ (deformation V t) z).toLinearMap := by
  rw [det_fderiv_deformation ((hV.differentiable (by simp)) z) t, jacobian_polynomial]
  simp [uniformJacobian, divergence, trace_realMatrix]

/-- This derivative is in the genuine global supremum norm. -/
theorem uniformJacobian_hasDerivAt_zero {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) :
    HasDerivAt (uniformJacobian hV hVc) (boundedDivergence hV hVc) 0 := by
  have h := ((hasDerivAt_const 0 (1 : CoefficientField)).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (boundedDivergence hV hVc))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).smul_const (boundedDifferentialDet hV hVc))
  simpa [uniformJacobian] using h

/-- The algebraic inverse Jacobian is a uniform coefficient field. Near
zero it agrees with pointwise reciprocal of the actual physical Jacobian. -/
def uniformInverseJacobian {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (t : ℝ) : CoefficientField :=
  Ring.inverse (uniformJacobian hV hVc t)

@[simp] theorem uniformInverseJacobian_zero {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) : uniformInverseJacobian hV hVc 0 = 1 := by
  simp [uniformInverseJacobian]

/-- Supremum-norm inverse-Jacobian first variation `−div V`. -/
theorem uniformInverseJacobian_hasDerivAt_zero {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) :
    HasDerivAt (uniformInverseJacobian hV hVc) (-boundedDivergence hV hVc) 0 := by
  have hJ := uniformJacobian_hasDerivAt_zero hV hVc
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : CoefficientFieldˣ)
  have hi' : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ CoefficientField (1 : CoefficientField) 1)
      (uniformJacobian hV hVc 0) := by simpa using hi
  convert hi'.comp_hasDerivAt 0 hJ using 1
  simp

private theorem coefficient_inverse_apply {f : CoefficientField} (hf : IsUnit f) (z : Plane) :
    (Ring.inverse f) z = (f z)⁻¹ := by
  rcases hf with ⟨u, rfl⟩
  rw [Ring.inverse_unit]
  apply eq_inv_of_mul_eq_one_left
  have h := congrArg (fun h : CoefficientField => h z) u.inv_val
  change (↑u⁻¹ : CoefficientField) z * (↑u : CoefficientField) z = 1 at h
  exact h

theorem uniformJacobian_eventually_isUnit {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (uniformJacobian hV hVc t) := by
  apply (uniformJacobian_hasDerivAt_zero hV hVc).continuousAt.tendsto.eventually
  rw [uniformJacobian_zero]
  exact Units.isOpen.mem_nhds isUnit_one

/-- Identification holds simultaneously at every physical point in a common
parameter neighborhood, as required for a uniform coefficient derivative. -/
theorem uniformInverseJacobian_eventually_apply {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ z : Plane,
      uniformInverseJacobian hV hVc t z =
        (LinearMap.det (fderiv ℝ (deformation V t) z).toLinearMap)⁻¹ := by
  filter_upwards [uniformJacobian_eventually_isUnit hV hVc] with t ht z
  rw [uniformInverseJacobian, coefficient_inverse_apply ht, uniformJacobian_apply]

/-- Numerators of the actual two-dimensional energy coefficient, as true
bounded continuous fields. -/
def uniformEnergyNumerator {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (i j : Fin 2) (t : ℝ) : CoefficientField :=
  let B := boundedDifferentialEntry hV hVc
  !![(1 + t • B 1 1) ^ 2 + (t • B 0 1) ^ 2,
      -((t • B 1 0) * (1 + t • B 1 1) + (t • B 0 1) * (1 + t • B 0 0));
     -((t • B 1 0) * (1 + t • B 1 1) + (t • B 0 1) * (1 + t • B 0 0)),
      (t • B 1 0) ^ 2 + (1 + t • B 0 0) ^ 2] i j

def uniformEnergyCoefficient {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (i j : Fin 2) (t : ℝ) : CoefficientField :=
  uniformEnergyNumerator hV hVc i j t * uniformInverseJacobian hV hVc t

def uniformEnergyVariation {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (i j : Fin 2) : CoefficientField :=
  (if i = j then boundedDivergence hV hVc else 0) -
    boundedDifferentialEntry hV hVc i j - boundedDifferentialEntry hV hVc j i

@[simp] theorem uniformEnergyVariation_apply {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (i j : Fin 2) (z : Plane) :
    uniformEnergyVariation hV hVc i j z = energyVariation (realMatrix (fderiv ℝ V z)) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [uniformEnergyVariation, energyVariation, boundedDivergence,
      Matrix.trace, Fin.sum_univ_two]

/-- Supremum-norm derivatives of every entry of the genuine fixed-domain
energy coefficient. The common-neighborhood identification with the physical
coefficient is proved separately below. -/
theorem uniformEnergyCoefficient_hasDerivAt_zero {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (i j : Fin 2) :
    HasDerivAt (uniformEnergyCoefficient hV hVc i j)
      (uniformEnergyVariation hV hVc i j) 0 := by
  let B := boundedDifferentialEntry hV hVc
  have hlin (p : CoefficientField) : HasDerivAt (fun t : ℝ => t • p) p 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const p
  have hone (p : CoefficientField) : HasDerivAt (fun t : ℝ => 1 + t • p) p 0 :=
    by simpa using (hasDerivAt_const 0 (1 : CoefficientField)).add (hlin p)
  have hdiag (p q : CoefficientField) : HasDerivAt
      (fun t : ℝ => (1 + t • p) ^ 2 + (t • q) ^ 2) (2 * p) 0 := by
    simpa [pow_two, two_mul] using ((hone p).mul (hone p)).add ((hlin q).mul (hlin q))
  have hoff (p q r s : CoefficientField) : HasDerivAt
      (fun t : ℝ => -((t • p) * (1 + t • q) + (t • r) * (1 + t • s)))
      (-(p + r)) 0 := by
    simpa using (((hlin p).mul (hone q)).add ((hlin r).mul (hone s))).neg
  have hi := uniformInverseJacobian_hasDerivAt_zero hV hVc
  fin_cases i <;> fin_cases j
  · have h := (hdiag (B 1 1) (B 0 1)).mul hi
    change HasDerivAt (fun t => ((1 + t • B 1 1) ^ 2 + (t • B 0 1) ^ 2) *
      uniformInverseJacobian hV hVc t) _ 0
    convert h using 1
    simp [uniformEnergyVariation, boundedDivergence, B]
    ring
  · have h := (hoff (B 1 0) (B 1 1) (B 0 1) (B 0 0)).mul hi
    change HasDerivAt (fun t => -((t • B 1 0) * (1 + t • B 1 1) +
      (t • B 0 1) * (1 + t • B 0 0)) * uniformInverseJacobian hV hVc t) _ 0
    convert h using 1
    simp [uniformEnergyVariation, B]
    ring
  · have h := (hoff (B 1 0) (B 1 1) (B 0 1) (B 0 0)).mul hi
    change HasDerivAt (fun t => -((t • B 1 0) * (1 + t • B 1 1) +
      (t • B 0 1) * (1 + t • B 0 0)) * uniformInverseJacobian hV hVc t) _ 0
    convert h using 1
    simp [uniformEnergyVariation, B]
    ring
  · have hN : HasDerivAt (fun t : ℝ => (t • B 1 0) ^ 2 + (1 + t • B 0 0) ^ 2)
        (2 * B 0 0) 0 := by
      simpa [pow_two, two_mul] using ((hlin (B 1 0)).mul (hlin (B 1 0))).add
        ((hone (B 0 0)).mul (hone (B 0 0)))
    have h := hN.mul hi
    change HasDerivAt (fun t => ((t • B 1 0) ^ 2 + (1 + t • B 0 0) ^ 2) *
      uniformInverseJacobian hV hVc t) _ 0
    convert h using 1
    simp [uniformEnergyVariation, boundedDivergence, B]
    ring

/-- The Banach-algebra coefficient agrees with the true physical matrix on
one parameter neighborhood simultaneously for all points and all entries. -/
theorem uniformEnergyCoefficient_eventually_apply {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ (i j : Fin 2) (z : Plane),
      uniformEnergyCoefficient hV hVc i j t z = physicalEnergyMatrix V t z i j := by
  filter_upwards [uniformJacobian_eventually_isUnit hV hVc] with t ht i j z
  have hnonzero : uniformJacobian hV hVc t z ≠ 0 := by
    rcases ht with ⟨u, hu⟩
    rw [← hu]
    intro hz
    have hh := congrArg (fun h : CoefficientField => h z) u.inv_val
    change (↑u⁻¹ : CoefficientField) z * (↑u : CoefficientField) z = 1 at hh
    rw [hz, mul_zero] at hh
    exact zero_ne_one hh
  have hJ : jacobian (realMatrix (fderiv ℝ V z)) t ≠ 0 := by
    rw [← det_fderiv_deformation ((hV.differentiable (by simp)) z) t,
      ← uniformJacobian_apply hV hVc t z]
    exact hnonzero
  rw [physicalEnergyMatrix_eq ((hV.differentiable (by simp)) z) t,
    energyMatrix_explicit _ hJ]
  have hinv : uniformInverseJacobian hV hVc t z =
      (jacobian (realMatrix (fderiv ℝ V z)) t)⁻¹ := by
    rw [uniformInverseJacobian, coefficient_inverse_apply ht, uniformJacobian_apply,
      det_fderiv_deformation ((hV.differentiable (by simp)) z) t]
  fin_cases i <;> fin_cases j <;>
    simp [uniformEnergyCoefficient, uniformEnergyNumerator, hinv, div_eq_mul_inv]

end Torsion.Shape

import Torsion.ShapeCoefficientScalar

/-! # Actual coefficient forms and their physical integrals -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Torsion.Shape
open HilbertDirichlet

theorem coefficientForm_bound (D : Set Plane) (i j : Fin 2) (a : CoefficientField)
    (p q : space D) : ‖coefficientForm D i j a p q‖ ≤ ‖a‖ * ‖p‖ * ‖q‖ := by
  rw [coefficientForm_apply_inner]
  apply (norm_inner_le_norm _ _).trans
  apply mul_le_mul
  · exact (multiplyL2_norm_le a _).trans
      (mul_le_mul_of_nonneg_left (scalarGradientMap_norm_le D j p) (norm_nonneg _))
  · exact scalarGradientMap_norm_le D i q
  · exact norm_nonneg _
  · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem coefficientForm_integrable (D : Set Plane) (i j : Fin 2) (a : CoefficientField)
    (p q : space D) : Integrable (fun z => a z * coordinate j (gradientMap D p z) *
      coordinate i (gradientMap D q z)) volume := by
  apply (multiplyL2_product_integrable a (scalarGradientMap D j p) (scalarGradientMap D i q)).congr
  filter_upwards [scalarGradientMap_ae D j p, scalarGradientMap_ae D i q] with z h1 h2
  rw [h1, h2]

theorem coefficientForm_apply (D : Set Plane) (i j : Fin 2) (a : CoefficientField)
    (p q : space D) : coefficientForm D i j a p q =
      ∫ z, a z * coordinate j (gradientMap D p z) * coordinate i (gradientMap D q z) := by
  rw [coefficientForm_apply_inner, multiplyL2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [scalarGradientMap_ae D j p, scalarGradientMap_ae D i q] with z h1 h2
  rw [h1, h2]

/-- Actual source integration against a bounded physical coefficient. -/
def coefficientForcing (D : Set Plane) (hD : MeasurableSet D) (hb : Bornology.IsBounded D) :
    CoefficientField →L[ℝ] space D →L[ℝ] ℝ :=
  coefficientForcingOfMaps (E := space D) coefficientMultiplyL2
    (indicatorConstLp 2 hD hb.measure_lt_top.ne (1 : ℝ)) (valueMap D)

theorem coefficientForcing_apply (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) (a : CoefficientField) (p : space D) :
    coefficientForcing D hD hb a p = ∫ z in D, a z * valueMap D p z := by
  let oneD : ScalarL2 := indicatorConstLp 2 hD hb.measure_lt_top.ne (1 : ℝ)
  rw [coefficientForcing, coefficientForcingOfMaps_apply]
  change inner (𝕜 := ℝ) (multiplyL2 a oneD) (valueMap D p) = _
  rw [multiplyL2_inner_selfadjoint]
  change inner (𝕜 := ℝ) (indicatorConstLp 2 hD hb.measure_lt_top.ne (1 : ℝ)) _ = _
  rw [L2.inner_indicatorConstLp_one hD hb.measure_lt_top.ne]
  apply integral_congr_ae
  exact ae_restrict_of_ae (multiplyL2_ae a (valueMap D p))

/-- The actual parameter-dependent energy form. -/
def shapeEnergy (D : Set Plane) {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (t : ℝ) : space D →L[ℝ] space D →L[ℝ] ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, coefficientForm D i j (uniformEnergyCoefficient hV hVc i j t)

def shapeEnergyVariation (D : Set Plane) {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) : space D →L[ℝ] space D →L[ℝ] ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, coefficientForm D i j (uniformEnergyVariation hV hVc i j)

def shapeForcing (D : Set Plane) (hD : MeasurableSet D) (hb : Bornology.IsBounded D)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (t : ℝ) :
    space D →L[ℝ] ℝ := coefficientForcing D hD hb (uniformJacobian hV hVc t)

def shapeForcingVariation (D : Set Plane) (hD : MeasurableSet D) (hb : Bornology.IsBounded D)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    space D →L[ℝ] ℝ := coefficientForcing D hD hb (boundedDivergence hV hVc)

set_option maxHeartbeats 1000000 in
theorem shapeEnergy_hasDerivAt_zero (D : Set Plane) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    HasDerivAt (shapeEnergy D hV hVc) (shapeEnergyVariation D hV hVc) 0 := by
  change HasDerivAt (fun t => shapeEnergy D hV hVc t) (shapeEnergyVariation D hV hVc) 0
  have hh (i j : Fin 2) : HasDerivAt
      (fun t => coefficientForm D i j (uniformEnergyCoefficient hV hVc i j t))
      (coefficientForm D i j (uniformEnergyVariation hV hVc i j)) 0 := by
    exact coefficientFormOfMaps_hasDerivAt (E := space D) coefficientMultiplyL2
      (scalarGradientMap D j) (scalarGradientMap D i)
      (uniformEnergyCoefficient_hasDerivAt_zero hV hVc i j)
  simpa only [shapeEnergy, shapeEnergyVariation, Fin.sum_univ_two] using
    (fourBilin_hasDerivAt (E := space D) (hh 0 0) (hh 0 1) (hh 1 0) (hh 1 1))

theorem shapeForcing_hasDerivAt_zero (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    HasDerivAt (shapeForcing D hD hb hV hVc) (shapeForcingVariation D hD hb hV hVc) 0 := by
  exact coefficientForcingOfMaps_hasDerivAt (E := space D) coefficientMultiplyL2
    (indicatorConstLp 2 hD hb.measure_lt_top.ne (1 : ℝ)) (valueMap D)
    (uniformJacobian_hasDerivAt_zero hV hVc)

@[simp] theorem shapeForcing_zero (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    shapeForcing D hD hb hV hVc 0 = forcingOn D hD hb := by
  ext p
  rw [shapeForcing, uniformJacobian_zero, coefficientForcing_apply, forcingOn_apply]
  simp

theorem shapeForcing_apply (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (t : ℝ) (p : space D) :
    shapeForcing D hD hb hV hVc t p =
      ∫ z in D, uniformJacobian hV hVc t z * valueMap D p z :=
  coefficientForcing_apply D hD hb _ p

theorem shapeForcingVariation_apply (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (p : space D) :
    shapeForcingVariation D hD hb hV hVc p =
      ∫ z in D, divergence V z * valueMap D p z := by
  simp only [shapeForcingVariation, coefficientForcing_apply, boundedDivergence_apply]

theorem shapeEnergy_apply (D : Set Plane) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (t : ℝ) (p q : space D) :
    shapeEnergy D hV hVc t p q =
      ∑ i : Fin 2, ∑ j : Fin 2, ∫ z, uniformEnergyCoefficient hV hVc i j t z *
        coordinate j (gradientMap D p z) * coordinate i (gradientMap D q z) := by
  simp only [shapeEnergy, ContinuousLinearMap.sum_apply, coefficientForm_apply]

theorem shapeEnergyVariation_apply (D : Set Plane) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (p q : space D) :
    shapeEnergyVariation D hV hVc p q =
      ∑ i : Fin 2, ∑ j : Fin 2, ∫ z, energyVariation (realMatrix (fderiv ℝ V z)) i j *
        coordinate j (gradientMap D p z) * coordinate i (gradientMap D q z) := by
  simp only [shapeEnergyVariation, ContinuousLinearMap.sum_apply, coefficientForm_apply, uniformEnergyVariation_apply]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
@[simp] theorem shapeEnergy_zero (D : Set Plane) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    shapeEnergy D hV hVc 0 = energy D := by
  have hzero (i j : Fin 2) : uniformEnergyCoefficient hV hVc i j 0 =
      if i = j then 1 else 0 := by
    fin_cases i <;> fin_cases j <;>
      simp [uniformEnergyCoefficient, uniformEnergyNumerator]
  ext p q
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [shapeEnergy, hzero, Fin.sum_univ_two]
  simp only [Fin.isValue, h01, h10, ↓reduceIte, map_zero, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply, zero_add, add_zero, coefficientForm_apply_inner,
    multiplyL2_one, energy_apply]
  exact (planeL2_inner_coordinates (gradientMap D p) (gradientMap D q)).symm



end Torsion.Shape

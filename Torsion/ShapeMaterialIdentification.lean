module

public import Torsion.ShapeMaterialSolution

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Identification with genuine deformed-domain weak torsion -/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix

namespace Torsion.Shape
open HilbertDirichlet

/-- The physical real matrix gives exactly the Euclidean energy pairing. -/
theorem realMatrix_inner_sum (L : Plane →L[ℝ] Plane) (p q : Plane) :
    inner (𝕜 := ℝ) (L p) q =
      ∑ i : Fin 2, ∑ j : Fin 2, realMatrix L i j * coordinate j p * coordinate i q := by
  have hp : L p = p.re • L (1 : Plane) + p.im • L Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    simpa [Complex.real_smul] using (Complex.re_add_im p).symm
  rw [hp]
  simp [Fin.sum_univ_two, coordinate, realMatrix, LinearMap.toMatrix_apply,
    Complex.coe_basisOneI, Complex.coe_basisOneI_repr, Complex.inner, Complex.mul_re,
    Complex.real_smul]
  ring

/-- The actual bounded shape form is the integral of an actual operator
whose matrix is its concrete coefficient field. -/
theorem coefficientMatrixForm_eq_operator_integral (D : Set Plane) (hD : MeasurableSet D)
    (a : Fin 2 → Fin 2 → CoefficientField) (L : Plane → Plane →L[ℝ] Plane)
    (hL : ∀ z i j, realMatrix (L z) i j = a i j z)
    (p q : space D) : (∑ i : Fin 2, ∑ j : Fin 2, coefficientForm D i j (a i j)) p q =
      ∫ z in D, inner (𝕜 := ℝ) (L z (gradientMap D p z)) (gradientMap D q z) := by
  let F : Fin 2 → Fin 2 → Plane → ℝ := fun i j z =>
    a i j z * coordinate j (gradientMap D p z) *
      coordinate i (gradientMap D q z)
  have hF (i j : Fin 2) : Integrable (F i j) volume :=
    coefficientForm_integrable D i j _ p q
  have hsum : Integrable (fun z => ∑ i : Fin 2, ∑ j : Fin 2, F i j z) volume := by
    apply integrable_finset_sum
    intro i _
    exact integrable_finset_sum _ (fun j _ => hF i j)
  have hpoint (z : Plane) : (∑ i : Fin 2, ∑ j : Fin 2, F i j z) =
      inner (𝕜 := ℝ) (L z (gradientMap D p z)) (gradientMap D q z) := by
    rw [realMatrix_inner_sum]
    simp only [hL]
    rfl
  have htotal : (∑ i : Fin 2, ∑ j : Fin 2, coefficientForm D i j (a i j)) p q =
      ∫ z, inner (𝕜 := ℝ) (L z (gradientMap D p z)) (gradientMap D q z) := by
    simp only [ContinuousLinearMap.sum_apply, coefficientForm_apply]
    calc
      _ = ∫ z, ∑ i : Fin 2, ∑ j : Fin 2, F i j z := by
        rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hF i j))]
        congr 1
        ext i
        rw [integral_finset_sum _ (fun j _ => hF i j)]
      _ = _ := integral_congr_ae (ae_of_all _ hpoint)
  rw [htotal]
  have hint : Integrable (fun z => inner (𝕜 := ℝ)
      (L z (gradientMap D p z)) (gradientMap D q z)) volume := by
    simpa only [hpoint] using hsum
  rw [← integral_add_compl hD hint]
  have hzero : (∫ z in Dᶜ, inner (𝕜 := ℝ)
      (L z (gradientMap D p z)) (gradientMap D q z)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [(memH10_coordinates q).gradient_ae_zero_off] with z hz
    simp [hz]
  rw [hzero, add_zero]


/-- The actual parameter-dependent shape form has its physical operator integral. -/
theorem shapeEnergy_eq_operator_integral (D : Set Plane) (hD : MeasurableSet D)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (t : ℝ) (L : Plane → Plane →L[ℝ] Plane)
    (hL : ∀ z i j, realMatrix (L z) i j = uniformEnergyCoefficient hV hVc i j t z)
    (p q : space D) : shapeEnergy D hV hVc t p q =
      ∫ z in D, inner (𝕜 := ℝ) (L z (gradientMap D p z)) (gradientMap D q z) :=
  coefficientMatrixForm_eq_operator_integral D hD _ L hL p q

/-- The differentiated form has the actual physical variation operator integral. -/
theorem shapeEnergyVariation_eq_operator_integral (D : Set Plane) (hD : MeasurableSet D)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (L : Plane → Plane →L[ℝ] Plane)
    (hL : ∀ z i j, realMatrix (L z) i j = uniformEnergyVariation hV hVc i j z)
    (p q : space D) : shapeEnergyVariation D hV hVc p q =
      ∫ z in D, inner (𝕜 := ℝ) (L z (gradientMap D p z)) (gradientMap D q z) :=
  coefficientMatrixForm_eq_operator_integral D hD _ L hL p q

/-- The constructed material solution is the unique graph solution of its
actual fixed-domain variational equation on a common parameter neighborhood. -/
theorem materialSolution_eventually_unique (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ p : space D,
      (∀ q : space D, shapeEnergy D hV hVc t p q = shapeForcing D hD hb hV hVc t q) →
      p = materialSolution D hD hb hV hVc t := by
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (materialOperator D hV hVc t) :=
    inverseSolution_eventually_isUnit (E := space D)
      (materialOperator_hasDerivAt_zero D hV hVc).continuousAt
      (materialOperator_zero_isUnit D hb hV hVc)
  filter_upwards [hnear] with t ht p hp
  have heq : materialOperator D hV hVc t p = materialSource D hD hb hV hVc t := by
    apply ext_inner_right ℝ
    intro q
    simpa only [materialOperator, rieszFormMap_apply_inner, materialSource,
      rieszSourceMap_apply_inner] using hp q
  have hcancel := Ring.inverse_mul_cancel (materialOperator D hV hVc t) ht
  have hcancelp := congrArg (fun A : space D →L[ℝ] space D => A p) hcancel
  change Ring.inverse (materialOperator D hV hVc t) (materialOperator D hV hVc t p) = p
    at hcancelp
  rw [← hcancelp, heq]
  rfl

/-- Every genuine weak torsion solution on a sufficiently small deformed
domain pulls back to the constructed differentiable material family. The
existence of the material derivative is consequently a theorem about the
original weak PDE, rather than an auxiliary family of unrelated vectors. -/
theorem exists_materialSolution_identification (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      ∃ e : Plane ≃ₜ Plane, (e : Plane → Plane) = deformation V t ∧
        ContDiff ℝ ∞ (e.symm : Plane → Plane) ∧
        ∀ (u : Plane → ℝ) (g : Plane → Plane),
          IsWeakTorsion (deformation V t '' D) u g →
          ∃ hm : MemH10 D (u ∘ e) (gradientPullback e g),
            ofMemH10 hm = materialSolution D hD hb hV hVc t := by
  obtain ⟨δ₀, hδ₀, hweak⟩ := exists_weakTorsion_pullback_deformation hV hVc
  have hnear := (materialSolution_eventually_unique D hD hb hV hVc).and
    (uniformEnergyCoefficient_eventually_apply hV hVc)
  obtain ⟨δ₁, hδ₁, hδnear⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro t ht
  obtain ⟨e, heq, heinv, hactual⟩ := hweak t (ht.trans_le (min_le_left _ _))
  have hnt := hδnear (by simpa [Real.dist_eq] using ht.trans_le (min_le_right δ₀ δ₁))
  have hmatrix (z : Plane) (i j : Fin 2) : realMatrix (pullbackEnergyOperator e z) i j =
      uniformEnergyCoefficient hV hVc i j t z := by
    rw [realMatrix_pullbackEnergyOperator_deformation hV t e heq heinv z]
    exact (hnt.2 i j z).symm
  refine ⟨e, heq, heinv, ?_⟩
  intro u g hu
  obtain ⟨hm, hequation⟩ := hactual D hD u g hu
  refine ⟨hm, hnt.1 (ofMemH10 hm) ?_⟩
  intro q
  have hgrad : (gradientMap D (ofMemH10 hm) : Plane → Plane) =ᵐ[volume]
      gradientPullback e g := by
    simpa only [gradientMap_ofMemH10] using hm.2.1.coeFn_toLp
  calc
    shapeEnergy D hV hVc t (ofMemH10 hm) q =
        ∫ z in D, inner (𝕜 := ℝ)
          (pullbackEnergyOperator e z (gradientMap D (ofMemH10 hm) z))
          (gradientMap D q z) :=
      shapeEnergy_eq_operator_integral D hD hV hVc t _ hmatrix _ _
    _ = ∫ z in D, inner (𝕜 := ℝ)
        (pullbackEnergyOperator e z (gradientPullback e g z)) (gradientMap D q z) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hgrad] with z hz
      rw [hz]
    _ = ∫ z in D, (fderiv ℝ (e : Plane → Plane) z).det * valueMap D q z :=
      hequation _ _ (memH10_coordinates q)
    _ = shapeForcing D hD hb hV hVc t q := by
      rw [shapeForcing_apply]
      simp only [uniformJacobian_apply, heq]

end Torsion.Shape

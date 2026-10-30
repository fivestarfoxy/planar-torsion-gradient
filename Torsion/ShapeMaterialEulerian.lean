module

public import Torsion.ShapeMaterialIdentification
public import Torsion.ShapeEulerianCommutator
public import Torsion.SobolevUniqueness

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The actual material derivative gives a localized Eulerian harmonic pair -/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion.Shape
open HilbertDirichlet

/-- The differentiated equation is an actual global compact-test equation
for the constructed weak-gradient representatives. -/
theorem materialDerivative_compact_test_equation (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    (∫ x, inner (𝕜 := ℝ) (gradientMap D (materialDerivative D hD hb hV hVc) x)
      (gradient ψ x)) = (∫ x, divergence V x * ψ x) -
        ∫ x, inner (𝕜 := ℝ)
          (energyVariationOperator V x (gradientMap D (materialSolution D hD hb hV hVc 0) x))
          (gradient ψ x) := by
  let q : space D := ofMemH10 hψ.memH10
  have hqv : (valueMap D q : Plane → ℝ) =ᵐ[volume] ψ := by
    exact hψ.memH10.1.coeFn_toLp
  have hqg : (gradientMap D q : Plane → Plane) =ᵐ[volume] gradient ψ := by
    exact hψ.memH10.2.1.coeFn_toLp
  have hmatrix (z : Plane) (i j : Fin 2) : realMatrix (energyVariationOperator V z) i j =
      uniformEnergyVariation hV hVc i j z := by
    rw [realMatrix_energyVariationOperator]
    exact (uniformEnergyVariation_apply hV hVc i j z).symm
  have heq := materialDerivative_variational D hD hb hV hVc q
  rw [energy_eq_setIntegral_of_measurable hD, shapeForcingVariation_apply,
    shapeEnergyVariation_eq_operator_integral D hD hV hVc _ hmatrix] at heq
  have hl : (∫ x in D, inner (𝕜 := ℝ)
      (gradientMap D (materialDerivative D hD hb hV hVc) x) (gradientMap D q x)) =
      ∫ x, inner (𝕜 := ℝ)
        (gradientMap D (materialDerivative D hD hb hV hVc) x) (gradient ψ x) := by
    trans ∫ x in D, inner (𝕜 := ℝ)
      (gradientMap D (materialDerivative D hD hb hV hVc) x) (gradient ψ x)
    · apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hqg] with x hx
      rw [hx]
    · apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hx (hψ.2.2 h)), inner_zero_right]
  have hr : (∫ x in D, divergence V x * valueMap D q x) = ∫ x, divergence V x * ψ x := by
    trans ∫ x in D, divergence V x * ψ x
    · apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hqv] with x hx
      rw [hx]
    · apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψ.2.2 h)), mul_zero]
  have ha : (∫ x in D, inner (𝕜 := ℝ)
      (energyVariationOperator V x (gradientMap D (materialSolution D hD hb hV hVc 0) x))
      (gradientMap D q x)) = ∫ x, inner (𝕜 := ℝ)
        (energyVariationOperator V x (gradientMap D (materialSolution D hD hb hV hVc 0) x))
        (gradient ψ x) := by
    trans ∫ x in D, inner (𝕜 := ℝ)
      (energyVariationOperator V x (gradientMap D (materialSolution D hD hb hV hVc 0) x))
      (gradient ψ x)
    · apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hqg] with x hx
      rw [hx]
    · apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hx (hψ.2.2 h)), inner_zero_right]
  rwa [hl, hr, ha] at heq

/-- The same actual derivative equation uses the classical gradient of any
smooth representative of the genuine base weak torsion solution. -/
theorem materialDerivative_compact_test_equation_classical (D : Set Plane)
    (hD : MeasurableSet D) (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hgu : ∀ x ∈ D, g x = gradient u x)
    {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    (∫ x, inner (𝕜 := ℝ) (gradientMap D (materialDerivative D hD hb hV hVc) x)
      (gradient ψ x)) = (∫ x, divergence V x * ψ x) -
        ∫ x, inner (𝕜 := ℝ) (energyVariationOperator V x (gradient u x)) (gradient ψ x) := by
  have heq := materialDerivative_compact_test_equation D hD hb hV hVc hψ
  have hgrad := (materialSolution_zero_isWeakTorsion D hD hb hV hVc).gradient_ae_eq hu
  have hi := (ae_restrict_iff' hD).mp hgrad
  have hh : (∫ x, inner (𝕜 := ℝ)
      (energyVariationOperator V x (gradientMap D (materialSolution D hD hb hV hVc 0) x))
      (gradient ψ x)) =
      ∫ x, inner (𝕜 := ℝ) (energyVariationOperator V x (gradient u x)) (gradient ψ x) := by
    apply integral_congr_ae
    filter_upwards [hi] with x hx
    by_cases hxD : x ∈ D
    · rw [hx hxD, hgu x hxD]
    · rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hxD (hψ.2.2 h))]
      simp
  rwa [hh] at heq

/-- Subtracting the genuine convective derivative from the constructed
material gradient gives the actual Eulerian harmonic compact-test equation. -/
theorem materialEulerian_smooth_test_equation (D : Set Plane) (hD : IsOpen D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hgu : ∀ x ∈ D, g x = gradient u x)
    (huc : ContDiffOn ℝ ∞ u D)
    (hlap : ∀ x ∈ D, WeakHarmonicRegularity.planarLaplacian u x = -1)
    {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    (∫ x, inner (𝕜 := ℝ)
      (gradientMap D (materialDerivative D hD.measurableSet hb hV hVc) x -
        gradient (fun y => inner (𝕜 := ℝ) (V y) (gradient u y)) x) (gradient ψ x)) = 0 := by
  apply eulerian_smooth_test_equation_of_material_equation hD hV huc hlap
    (Lp.memLp (gradientMap D (materialDerivative D hD.measurableSet hb hV hVc))) _ hψ
  intro φ hφ
  exact materialDerivative_compact_test_equation_classical D hD.measurableSet hb hV hVc hu hgu hφ

/-- Genuine weak harmonic localization of the actual Eulerian derivative
inside any relatively compact open subregion of the reference domain. -/
theorem exists_materialEulerian_weakHarmonic (D : Set Plane) (hD : IsOpen D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hgu : ∀ x ∈ D, g x = gradient u x)
    (huc : ContDiffOn ℝ ∞ u D)
    (hlap : ∀ x ∈ D, WeakHarmonicRegularity.planarLaplacian u x = -1)
    {U : Set Plane} (hU : IsOpen U) (hUc : IsCompact (closure U)) (hUD : closure U ⊆ D) :
    ∃ c : Plane → ℝ, IsTest D c ∧
      (∀ x ∈ U, c x = inner (𝕜 := ℝ) (V x) (gradient u x)) ∧
      IsWeakHarmonicOn U
        (fun x => valueMap D (materialDerivative D hD.measurableSet hb hV hVc) x - c x)
        (fun x => gradientMap D (materialDerivative D hD.measurableSet hb hV hVc) x - gradient c x) := by
  apply exists_localized_eulerian_weakHarmonic hD hV huc hlap
    (memH10_coordinates (materialDerivative D hD.measurableSet hb hV hVc)) hU hUc hUD
  intro φ hφ
  exact materialDerivative_compact_test_equation_classical D hD.measurableSet hb hV hVc hu hgu hφ

end Torsion.Shape

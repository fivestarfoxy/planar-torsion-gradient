module

public import Torsion.ShapeCoefficientForms
public import Torsion.ShapeMaterialBase
public import Torsion.ShapeEnergyOperatorMatrix

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Material differentiability on the original weak Dirichlet graph

The actual uniform shape coefficients define bounded forms on the existing
Hilbert graph. The base Dirichlet form is invertible by its proved Poincaré
and Lax--Milgram construction. Openness and differentiation of the Banach
algebra inverse construct the material solution family and its strong H¹
derivative. The differentiated equation is proved for every original graph
test.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion.Shape
open HilbertDirichlet

/-- The actual shape-dependent fixed-domain operator. -/
def materialOperator (D : Set Plane) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (t : ℝ) :
    space D →L[ℝ] space D := rieszFormMap D (shapeEnergy D hV hVc t)

def materialOperatorVariation (D : Set Plane) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) : space D →L[ℝ] space D :=
  rieszFormMap D (shapeEnergyVariation D hV hVc)

def materialSource (D : Set Plane) (hD : MeasurableSet D) (hb : Bornology.IsBounded D)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (t : ℝ) :
    space D := rieszSourceMap D (shapeForcing D hD hb hV hVc t)

def materialSourceVariation (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) : space D :=
  rieszSourceMap D (shapeForcingVariation D hD hb hV hVc)

theorem materialOperator_hasDerivAt_zero (D : Set Plane) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    HasDerivAt (materialOperator D hV hVc) (materialOperatorVariation D hV hVc) 0 :=
  rieszFormMap_comp_hasDerivAt D (shapeEnergy_hasDerivAt_zero D hV hVc)

theorem materialSource_hasDerivAt_zero (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    HasDerivAt (materialSource D hD hb hV hVc) (materialSourceVariation D hD hb hV hVc) 0 :=
  rieszSourceMap_comp_hasDerivAt D (shapeForcing_hasDerivAt_zero D hD hb hV hVc)

theorem materialOperator_zero (D : Set Plane) (hb : Bornology.IsBounded D)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    materialOperator D hV hVc 0 = (materialBaseUnit D hb : space D →L[ℝ] space D) := by
  unfold materialOperator
  rw [shapeEnergy_zero]
  rfl

theorem materialOperator_zero_isUnit (D : Set Plane) (hb : Bornology.IsBounded D)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    IsUnit (materialOperator D hV hVc 0) := by
  rw [materialOperator_zero D hb hV hVc]
  exact Units.isUnit _

/-- The actual inverse-operator solution of the fixed-domain problem.
Only its values on the proved unit neighborhood are used. -/
def materialSolution (D : Set Plane) (hD : MeasurableSet D) (hb : Bornology.IsBounded D)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (t : ℝ) :
    space D := Ring.inverse (materialOperator D hV hVc t) (materialSource D hD hb hV hVc t)

/-- The constructed strong material derivative, in the original H¹₀ norm. -/
def materialDerivative (D : Set Plane) (hD : MeasurableSet D) (hb : Bornology.IsBounded D)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) : space D :=
  Ring.inverse (materialOperator D hV hVc 0)
    (materialSourceVariation D hD hb hV hVc -
      materialOperatorVariation D hV hVc (materialSolution D hD hb hV hVc 0))

/-- Strong H¹ material differentiability follows from the actual coefficient
derivatives and base coercivity, with no material differentiability premise. -/
theorem materialSolution_hasDerivAt_zero (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    HasDerivAt (materialSolution D hD hb hV hVc) (materialDerivative D hD hb hV hVc) 0 :=
  inverseSolution_hasDerivAt (E := space D) (materialOperator_hasDerivAt_zero D hV hVc)
    (materialSource_hasDerivAt_zero D hD hb hV hVc) (materialOperator_zero_isUnit D hb hV hVc)

theorem materialSolution_eventually_variational (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ q : space D,
      shapeEnergy D hV hVc t (materialSolution D hD hb hV hVc t) q =
        shapeForcing D hD hb hV hVc t q := by
  have heq := inverseSolution_eventually_equation (E := space D)
    (materialOperator_hasDerivAt_zero D hV hVc).continuousAt
    (materialOperator_zero_isUnit D hb hV hVc) (f := materialSource D hD hb hV hVc)
  filter_upwards [heq] with t ht q
  have hi := congrArg (fun p : space D => inner (𝕜 := ℝ) p q) ht
  simpa only [materialSolution, materialOperator, rieszFormMap_apply_inner, materialSource,
    rieszSourceMap_apply_inner] using hi

/-- At the base parameter the constructed graph vector is an actual weak
Dirichlet torsion solution on the original domain. -/
theorem materialSolution_zero_isWeakTorsion (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    IsWeakTorsion D (valueMap D (materialSolution D hD hb hV hVc 0))
      (gradientMap D (materialSolution D hD hb hV hVc 0)) := by
  apply variational_isWeakTorsion_of_bounded hD hb
  intro q
  have h := (materialSolution_eventually_variational D hD hb hV hVc).self_of_nhds q
  simpa only [shapeEnergy_zero, shapeForcing_zero] using h

/-- The strong material derivative passes through the actual L² value map. -/
theorem materialValue_hasDerivAt_zero (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    HasDerivAt (fun t : ℝ => valueMap D (materialSolution D hD hb hV hVc t))
      (valueMap D (materialDerivative D hD hb hV hVc)) 0 :=
  valueMap_comp_hasDerivAt D (materialSolution_hasDerivAt_zero D hD hb hV hVc)

/-- In particular the true weak-gradient fields have a strong L² parameter
derivative, as required by the marked-flux difference-quotient argument. -/
theorem materialGradient_hasDerivAt_zero (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    HasDerivAt (fun t : ℝ => gradientMap D (materialSolution D hD hb hV hVc t))
      (gradientMap D (materialDerivative D hD hb hV hVc)) 0 :=
  gradientMap_comp_hasDerivAt D (materialSolution_hasDerivAt_zero D hD hb hV hVc)

/-- The differentiated fixed-domain weak equation, for every original H¹₀
graph test. Its coefficients are the actual proved shape variations. -/
theorem materialDerivative_variational (D : Set Plane) (hD : MeasurableSet D)
    (hb : Bornology.IsBounded D) {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (q : space D) :
    energy D (materialDerivative D hD hb hV hVc) q =
      shapeForcingVariation D hD hb hV hVc q -
        shapeEnergyVariation D hV hVc (materialSolution D hD hb hV hVc 0) q := by
  have hu := materialOperator_zero_isUnit D hb hV hVc
  have hh := Ring.mul_inverse_cancel (materialOperator D hV hVc 0) hu
  have heq := congrArg (fun A : space D →L[ℝ] space D =>
    A (materialSourceVariation D hD hb hV hVc -
      materialOperatorVariation D hV hVc (materialSolution D hD hb hV hVc 0))) hh
  change materialOperator D hV hVc 0 (materialDerivative D hD hb hV hVc) = _ at heq
  have hi := congrArg (fun p : space D => inner (𝕜 := ℝ) p q) heq
  simpa only [materialOperator, rieszFormMap_apply_inner, shapeEnergy_zero,
    ContinuousLinearMap.one_apply, inner_sub_left, materialSourceVariation, rieszSourceMap_apply_inner,
    materialOperatorVariation] using hi

end Torsion.Shape

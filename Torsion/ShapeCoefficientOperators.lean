import Torsion.ShapeUniformCoefficients
import Torsion.HilbertDirichlet
import Torsion.L2Dominated

/-! # Actual coefficient forms on the original Dirichlet Hilbert graph -/

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Shape
open HilbertDirichlet

abbrev ScalarL2 := Lp ℝ 2 (volume : Measure Plane)

private theorem multiplier_memLp (a : CoefficientField) (f : ScalarL2) :
    MemLp (fun z => a z * f z) 2 volume := by
  simpa only [smul_eq_mul] using memLp_bounded_coeff_smul a.continuous.aestronglyMeasurable
    (Lp.memLp f) (ae_of_all _ a.norm_coe_le_norm)

/-- Multiplication by the genuine bounded continuous coefficient. -/
def multiplyL2 (a : CoefficientField) (f : ScalarL2) : ScalarL2 :=
  (multiplier_memLp a f).toLp (fun z => a z * f z)

theorem multiplyL2_ae (a : CoefficientField) (f : ScalarL2) :
    multiplyL2 a f =ᵐ[volume] fun z => a z * f z :=
  MemLp.coeFn_toLp _

theorem multiplyL2_norm_le (a : CoefficientField) (f : ScalarL2) :
    ‖multiplyL2 a f‖ ≤ ‖a‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplyL2_ae a f] with z hz
  rw [hz, norm_mul]
  exact mul_le_mul_of_nonneg_right (a.norm_coe_le_norm z) (norm_nonneg _)

/-- Bounded multiplication is bilinear in the actual coefficient and L² field. -/
def coefficientMultiplyL2 : CoefficientField →L[ℝ] ScalarL2 →L[ℝ] ScalarL2 :=
  LinearMap.mkContinuous₂ (LinearMap.mk₂ ℝ multiplyL2
    (by
      intro a b f
      apply Lp.ext
      filter_upwards [multiplyL2_ae (a + b) f, multiplyL2_ae a f,
        multiplyL2_ae b f, Lp.coeFn_add (multiplyL2 a f) (multiplyL2 b f)] with z h1 h2 h3 h4
      simp only [h1, h4, Pi.add_apply, h2, h3, BoundedContinuousFunction.add_apply, add_mul])
    (by
      intro c a f
      apply Lp.ext
      filter_upwards [multiplyL2_ae (c • a) f, multiplyL2_ae a f,
        Lp.coeFn_smul c (multiplyL2 a f)] with z h1 h2 h3
      simp [h1, h2, h3, mul_assoc])
    (by
      intro a f g
      apply Lp.ext
      filter_upwards [multiplyL2_ae a (f + g), multiplyL2_ae a f,
        multiplyL2_ae a g, Lp.coeFn_add f g,
        Lp.coeFn_add (multiplyL2 a f) (multiplyL2 a g)] with z h1 h2 h3 h4 h5
      simp only [h1, h4, h5, Pi.add_apply, h2, h3, mul_add])
    (by
      intro c a f
      apply Lp.ext
      filter_upwards [multiplyL2_ae a (c • f), multiplyL2_ae a f,
        Lp.coeFn_smul c f, Lp.coeFn_smul c (multiplyL2 a f)] with z h1 h2 h3 h4
      simp [h1, h2, h3, h4]
      ring)) 1 (fun a f => by simpa using multiplyL2_norm_le a f)

@[simp] theorem coefficientMultiplyL2_apply (a : CoefficientField) (f : ScalarL2) :
    coefficientMultiplyL2 a f = multiplyL2 a f := rfl

@[simp] theorem multiplyL2_one (f : ScalarL2) : multiplyL2 1 f = f := by
  apply Lp.ext
  exact (multiplyL2_ae 1 f).mono (fun z hz => by simpa using hz)

/-- The physical real-coordinate projection. -/
def coordinate (i : Fin 2) : Plane →L[ℝ] ℝ := if i = 0 then Complex.reCLM else Complex.imCLM

/-- Coordinate fields of the original actual weak gradient. -/
def scalarGradientMap (D : Set Plane) (i : Fin 2) : space D →L[ℝ] ScalarL2 :=
  ((coordinate i).compLpL 2 volume).comp (gradientMap D)

theorem scalarGradientMap_ae (D : Set Plane) (i : Fin 2) (p : space D) :
    scalarGradientMap D i p =ᵐ[volume] fun z => coordinate i (gradientMap D p z) :=
  (coordinate i).coeFn_compLp _

theorem scalarGradientMap_norm_le (D : Set Plane) (i : Fin 2) (p : space D) :
    ‖scalarGradientMap D i p‖ ≤ ‖p‖ := by
  apply le_trans _ (gradient_norm_le D p)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [scalarGradientMap_ae D i p] with z hz
  rw [hz]
  fin_cases i
  · simpa [coordinate] using Complex.abs_re_le_norm (gradientMap D p z)
  · simpa [coordinate] using Complex.abs_im_le_norm (gradientMap D p z)

def coefficientFormOfMaps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : CoefficientField →L[ℝ] ScalarL2 →L[ℝ] ScalarL2)
    (G H : E →L[ℝ] ScalarL2) :
    CoefficientField →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := by
  let Cj : (ScalarL2 →L[ℝ] ScalarL2) →L[ℝ] (E →L[ℝ] ScalarL2) :=
    (ContinuousLinearMap.compL ℝ (E) ScalarL2 ScalarL2).flip G
  let K : (E →L[ℝ] ScalarL2) →L[ℝ] (E →L[ℝ] ScalarL2 →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (E) ScalarL2 (ScalarL2 →L[ℝ] ℝ)) (innerSL ℝ)
  let Ci : (ScalarL2 →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (E) ScalarL2 ℝ).flip H
  let P : (E →L[ℝ] ScalarL2 →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (E) (ScalarL2 →L[ℝ] ℝ) (E →L[ℝ] ℝ)) Ci
  exact P.comp (K.comp (Cj.comp M))

@[simp] theorem coefficientFormOfMaps_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : CoefficientField →L[ℝ] ScalarL2 →L[ℝ] ScalarL2)
    (G H : E →L[ℝ] ScalarL2) (a : CoefficientField) (p q : E) :
    coefficientFormOfMaps M G H a p q = inner (𝕜:=ℝ) (M a (G p)) (H q) := rfl

def coefficientForcingOfMaps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : CoefficientField →L[ℝ] ScalarL2 →L[ℝ] ScalarL2)
    (oneD : ScalarL2) (G : E →L[ℝ] ScalarL2) : CoefficientField →L[ℝ] E →L[ℝ] ℝ := by
  let A : CoefficientField →L[ℝ] ScalarL2 := M.flip oneD
  let P : (ScalarL2 →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E ScalarL2 ℝ).flip G
  exact P.comp ((innerSL ℝ).comp A)

@[simp] theorem coefficientForcingOfMaps_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : CoefficientField →L[ℝ] ScalarL2 →L[ℝ] ScalarL2)
    (oneD : ScalarL2) (G : E →L[ℝ] ScalarL2) (a : CoefficientField) (p : E) :
    coefficientForcingOfMaps M oneD G a p = inner (𝕜:=ℝ) (M a oneD) (G p) := rfl

theorem coefficientFormOfMaps_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : CoefficientField →L[ℝ] ScalarL2 →L[ℝ] ScalarL2) (G H : E →L[ℝ] ScalarL2)
    {a : ℝ → CoefficientField} {a' : CoefficientField} {t : ℝ} (ha : HasDerivAt a a' t) :
    HasDerivAt (fun s => coefficientFormOfMaps M G H (a s))
      (coefficientFormOfMaps M G H a') t := by
  have hL : HasFDerivAt (coefficientFormOfMaps M G H) (coefficientFormOfMaps M G H) (a t) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := CoefficientField)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (coefficientFormOfMaps M G H)
  simpa only [Function.comp_apply] using
    HasFDerivAt.comp_hasDerivAt (E := E →L[ℝ] E →L[ℝ] ℝ) (F := CoefficientField) t hL ha

theorem coefficientForcingOfMaps_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : CoefficientField →L[ℝ] ScalarL2 →L[ℝ] ScalarL2) (oneD : ScalarL2) (G : E →L[ℝ] ScalarL2)
    {a : ℝ → CoefficientField} {a' : CoefficientField} {t : ℝ} (ha : HasDerivAt a a' t) :
    HasDerivAt (fun s => coefficientForcingOfMaps M oneD G (a s))
      (coefficientForcingOfMaps M oneD G a') t := by
  have hL : HasFDerivAt (coefficientForcingOfMaps M oneD G)
      (coefficientForcingOfMaps M oneD G) (a t) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := CoefficientField)
      (F := E →L[ℝ] ℝ) (coefficientForcingOfMaps M oneD G)
  simpa only [Function.comp_apply] using
    HasFDerivAt.comp_hasDerivAt (E := E →L[ℝ] ℝ) (F := CoefficientField) t hL ha

/-- Actual coefficient integration on the original Dirichlet Hilbert graph. -/
def coefficientForm (D : Set Plane) (i j : Fin 2) :
    CoefficientField →L[ℝ] space D →L[ℝ] space D →L[ℝ] ℝ :=
  coefficientFormOfMaps (E := space D) coefficientMultiplyL2 (scalarGradientMap D j) (scalarGradientMap D i)

theorem coefficientForm_apply_inner (D : Set Plane) (i j : Fin 2) (a : CoefficientField)
    (p q : space D) : coefficientForm D i j a p q =
      inner (𝕜 := ℝ) (multiplyL2 a (scalarGradientMap D j p)) (scalarGradientMap D i q) :=
  coefficientFormOfMaps_apply (E := space D) coefficientMultiplyL2 (scalarGradientMap D j)
    (scalarGradientMap D i) a p q


end Torsion.Shape

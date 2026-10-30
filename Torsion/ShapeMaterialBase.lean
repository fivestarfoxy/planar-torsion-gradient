import Torsion.HilbertDirichlet
import Torsion.ShapeMaterialInverse
import Torsion.ShapeMaterialGeneric

/-! # The genuine base Dirichlet operator for material differentiation -/
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
open Set
namespace Torsion.Shape
open HilbertDirichlet

def rieszSourceMap (D : Set Plane) : NormedSpace.Dual ℝ (space D) →L[ℝ] space D :=
  hilbertRieszSourceMap (space D)

@[simp] theorem rieszSourceMap_apply_inner (D : Set Plane)
    (f : NormedSpace.Dual ℝ (space D)) (q : space D) :
    inner (𝕜 := ℝ) (rieszSourceMap D f) q = f q :=
  hilbertRieszSourceMap_apply_inner (space D) f q

def rieszFormMap (D : Set Plane) :
    (space D →L[ℝ] space D →L[ℝ] ℝ) →L[ℝ] (space D →L[ℝ] space D) :=
  hilbertRieszFormMap (space D)

@[simp] theorem rieszFormMap_apply_inner (D : Set Plane)
    (B : space D →L[ℝ] space D →L[ℝ] ℝ) (p q : space D) :
    inner (𝕜 := ℝ) (rieszFormMap D B p) q = B p q :=
  hilbertRieszFormMap_apply_inner (space D) B p q

theorem rieszFormMap_comp_hasDerivAt (D : Set Plane)
    {B : ℝ → space D →L[ℝ] space D →L[ℝ] ℝ}
    {B' : space D →L[ℝ] space D →L[ℝ] ℝ} (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun t : ℝ => rieszFormMap D (B t)) (rieszFormMap D B') 0 :=
  hilbertRieszFormMap_comp_hasDerivAt (space D) hB

theorem rieszSourceMap_comp_hasDerivAt (D : Set Plane)
    {f : ℝ → NormedSpace.Dual ℝ (space D)} {f' : NormedSpace.Dual ℝ (space D)}
    (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun t : ℝ => rieszSourceMap D (f t)) (rieszSourceMap D f') 0 :=
  hilbertRieszSourceMap_comp_hasDerivAt (space D) hf

theorem valueMap_comp_hasDerivAt (D : Set Plane) {p : ℝ → space D} {p' : space D}
    (hp : HasDerivAt p p' 0) :
    HasDerivAt (fun t : ℝ => valueMap D (p t)) (valueMap D p') 0 :=
  fixedCLM_comp_hasDerivAt (E := space D) (F := ValueL2) (valueMap D) hp

theorem gradientMap_comp_hasDerivAt (D : Set Plane) {p : ℝ → space D} {p' : space D}
    (hp : HasDerivAt p p' 0) :
    HasDerivAt (fun t : ℝ => gradientMap D (p t)) (gradientMap D p') 0 :=
  fixedCLM_comp_hasDerivAt (E := space D) (F := GradientL2) (gradientMap D) hp

/-- The base energy operator is an actual unit by the proved Lax--Milgram
 equivalence, including the empty graph case. -/
def materialBaseUnit (D : Set Plane) (hb : Bornology.IsBounded D) :
    (space D →L[ℝ] space D)ˣ where
  val := (energy_coercive_of_bounded hb).continuousLinearEquivOfBilin.toContinuousLinearMap
  inv := (energy_coercive_of_bounded hb).continuousLinearEquivOfBilin.symm.toContinuousLinearMap
  val_inv := by
    apply ContinuousLinearMap.ext
    intro p
    exact (energy_coercive_of_bounded hb).continuousLinearEquivOfBilin.apply_symm_apply p
  inv_val := by
    apply ContinuousLinearMap.ext
    intro p
    exact (energy_coercive_of_bounded hb).continuousLinearEquivOfBilin.symm_apply_apply p

end Torsion.Shape

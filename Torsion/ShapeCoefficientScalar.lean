import Torsion.ShapeCoefficientOperators

/-! # Scalar L² identities for bounded shape multipliers -/
noncomputable section
open MeasureTheory
namespace Torsion.Shape

theorem multiplyL2_product_integrable (a : CoefficientField) (f g : ScalarL2) :
    Integrable (fun z => a z * f z * g z) volume := by
  apply (L2.integrable_inner (𝕜 := ℝ) (multiplyL2 a f) g).congr
  filter_upwards [multiplyL2_ae a f] with z hz
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hz]
  ring

theorem multiplyL2_inner_eq_integral (a : CoefficientField) (f g : ScalarL2) :
    inner (𝕜 := ℝ) (multiplyL2 a f) g = ∫ z, a z * f z * g z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplyL2_ae a f] with z hz
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hz]
  ring

theorem multiplyL2_inner_selfadjoint (a : CoefficientField) (f g : ScalarL2) :
    inner (𝕜 := ℝ) (multiplyL2 a f) g =
      inner (𝕜 := ℝ) f (multiplyL2 a g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplyL2_ae a f, multiplyL2_ae a g] with z hf hg
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hf, hg]
  ring

/-- Splitting the genuine planar L² inner product into its real coordinates. -/
theorem planeL2_inner_coordinates (f g : HilbertDirichlet.GradientL2) :
    inner (𝕜 := ℝ) f g =
      inner (𝕜 := ℝ) ((coordinate 0).compLpL 2 volume f) ((coordinate 0).compLpL 2 volume g) +
      inner (𝕜 := ℝ) ((coordinate 1).compLpL 2 volume f) ((coordinate 1).compLpL 2 volume g) := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def,
    ← integral_add (L2.integrable_inner ((coordinate 0).compLpL 2 volume f)
      ((coordinate 0).compLpL 2 volume g))
      (L2.integrable_inner ((coordinate 1).compLpL 2 volume f)
      ((coordinate 1).compLpL 2 volume g))]
  apply integral_congr_ae
  filter_upwards [(coordinate 0).coeFn_compLpL f, (coordinate 0).coeFn_compLpL g,
    (coordinate 1).coeFn_compLpL f, (coordinate 1).coeFn_compLpL g] with z h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  simp [coordinate, Complex.inner, Complex.mul_re]

/-- Finite addition of bilinear-form derivatives, with the operator-space
norm handled before specializing to a concrete Sobolev graph. -/
theorem fourBilin_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B00 B01 B10 B11 : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {C00 C01 C10 C11 : E →L[ℝ] E →L[ℝ] ℝ}
    (h00 : HasDerivAt B00 C00 0) (h01 : HasDerivAt B01 C01 0)
    (h10 : HasDerivAt B10 C10 0) (h11 : HasDerivAt B11 C11 0) :
    HasDerivAt (fun t => B00 t + B01 t + (B10 t + B11 t))
      (C00 + C01 + (C10 + C11)) 0 :=
  HasDerivAt.add (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
    (HasDerivAt.add (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) h00 h01)
    (HasDerivAt.add (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) h10 h11)

end Torsion.Shape

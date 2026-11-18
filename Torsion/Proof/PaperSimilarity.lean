module

public import Torsion.CanonicalOptimization
public import Torsion.TorsionIsometry
public import Torsion.TorsionTranslation
public import Torsion.DilationWeak

@[expose] public section

/-!
# Similarities and equality in the sharp torsion bound

The reverse implication of Theorem 1.2 uses the actual weak-gradient norm
and the normalized Cauchy image from Theorem 1.1.
-/

noncomputable section
open Set

namespace Torsion
namespace ConvexDomain

/-- The image of a convex domain under the similarity `z ↦ p + s • U z`. -/
def similarityImage (D : ConvexDomain) (p : Plane) (s : ℝ) (hs : 0 < s)
    (U : Plane ≃ₗᵢ[ℝ] Plane) : ConvexDomain :=
  (((D.isometryPreimage U.symm).dilate s hs).translate p)

theorem similarityImage_carrier (D : ConvexDomain) (p : Plane) (s : ℝ)
    (hs : 0 < s) (U : Plane ≃ₗᵢ[ℝ] Plane) :
    (D.similarityImage p s hs U).carrier = (fun z => p + s • U z) '' D.carrier := by
  have hU : (D.isometryPreimage U.symm).carrier = U '' D.carrier := by
    ext x
    constructor
    · intro hx
      exact ⟨U.symm x, hx, U.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change U.symm (U y) ∈ D.carrier
      simpa only [U.symm_apply_apply] using hy
  simp only [similarityImage, translate_carrier, dilate_carrier, hU, Set.image_image,
    Complex.real_smul, add_comm]

theorem similarityImage_area (D : ConvexDomain) (p : Plane) (s : ℝ)
    (hs : 0 < s) (U : Plane ≃ₗᵢ[ℝ] Plane) :
    (D.similarityImage p s hs U).area = s ^ 2 * D.area := by
  rw [similarityImage, translate_area, dilate_area, isometryPreimage_area]

/-- The positive scale of a similarity between two area-one domains is one. -/
theorem scale_eq_one_of_similarityImage_area_one (D : ConvexDomain) (p : Plane)
    (s : ℝ) (hs : 0 < s) (U : Plane ≃ₗᵢ[ℝ] Plane)
    (hD : D.area = 1) (himage : (D.similarityImage p s hs U).area = 1) : s = 1 := by
  rw [similarityImage_area, hD, mul_one] at himage
  calc
    s = Real.sqrt (s ^ 2) := (Real.sqrt_sq hs.le).symm
    _ = 1 := by rw [himage, Real.sqrt_one]

theorem eq_of_carrier_eq {D E : ConvexDomain} (h : D.carrier = E.carrier) : D = E := by
  cases D
  cases E
  cases h
  rfl

end ConvexDomain

theorem DirichletTheory.G_similarityImage (T : DirichletTheory) (D : ConvexDomain)
    (p : Plane) (s : ℝ) (hs : 0 < s) (U : Plane ≃ₗᵢ[ℝ] Plane) :
    T.G (D.similarityImage p s hs U) = ENNReal.ofReal s * T.G D := by
  rw [ConvexDomain.similarityImage, T.G_translate, T.G_dilate, T.G_isometryPreimage]

open Spectral

/-- Every similarity image of the normalized spectral optimizer realizes equality in
the sharp inequality, including the images under orientation-reversing isometries. -/
theorem second_sharp_equality_of_similarity (D : ConvexDomain) (p : Plane)
    (s : ℝ) (hs : 0 < s) (U : Plane ≃ₗᵢ[ℝ] Plane)
    (hD : D.carrier = (fun z => p + s • U z) ''
      normalizedImage secondEigenvalue secondEigenfunction) :
    torsionTheory.G D = ENNReal.ofReal
      (spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt D.area) := by
  obtain ⟨E, hE, harea, hG⟩ := second_exact_value.2
  have hDE : D = E.similarityImage p s hs U := by
    apply ConvexDomain.eq_of_carrier_eq
    rwa [ConvexDomain.similarityImage_carrier, hE]
  rw [hDE, torsionTheory.G_similarityImage, ConvexDomain.similarityImage_area,
    harea, mul_one, Real.sqrt_sq hs.le, hG, ← ENNReal.ofReal_mul hs.le, mul_comm s]

/-- To classify equality at all areas it suffices to classify area-one maximizers up to
Euclidean motions. Dilating an arbitrary maximizer to area one also rescales its translation
vector when the normalization is undone. -/
theorem second_similarity_of_area_one_rigidity
    (hunit : ∀ E : ConvexDomain, E.area = 1 →
      torsionTheory.G E = ENNReal.ofReal (spectralConstant secondEigenvalue secondEigenfunction) →
      ∃ (q : Plane) (U : Plane ≃ₗᵢ[ℝ] Plane),
        E.carrier = (fun z => q + U z) '' normalizedImage secondEigenvalue secondEigenfunction)
    (D : ConvexDomain) (hD : torsionTheory.G D = ENNReal.ofReal
      (spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt D.area)) :
    ∃ (p : Plane) (s : ℝ), 0 < s ∧ ∃ (U : Plane ≃ₗᵢ[ℝ] Plane),
      D.carrier = (fun z => p + s • U z) '' normalizedImage secondEigenvalue secondEigenfunction := by
  have hA : 0 < D.area := ENNReal.toReal_pos
    (D.isOpen.measure_ne_zero MeasureTheory.volume D.nonempty) D.bounded.measure_lt_top.ne
  let t := Real.sqrt D.area
  have ht : 0 < t := Real.sqrt_pos.mpr hA
  let E := D.dilate t⁻¹ (inv_pos.mpr ht)
  have hEarea : E.area = 1 := by
    rw [ConvexDomain.dilate_area, inv_pow, Real.sq_sqrt hA.le, inv_mul_cancel₀ hA.ne']
  have hEG : torsionTheory.G E =
      ENNReal.ofReal (spectralConstant secondEigenvalue secondEigenfunction) := by
    change torsionTheory.G (D.dilate t⁻¹ _) = _
    rw [torsionTheory.G_dilate, hD, ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
    congr 1
    change t⁻¹ * (_ * t) = _
    rw [mul_comm _ t, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  obtain ⟨q, U, hEU⟩ := hunit E hEarea hEG
  refine ⟨t • q, t, ht, U, ?_⟩
  calc
    D.carrier = (fun z : Plane => t • z) '' E.carrier := by
      change D.carrier = (fun z : Plane => t • z) '' (fun z : Plane => t⁻¹ • z) '' D.carrier
      simp only [Set.image_image, smul_smul, mul_inv_cancel₀ ht.ne', one_smul, Set.image_id']
    _ = _ := by rw [hEU]; simp only [Set.image_image, smul_add]

end Torsion

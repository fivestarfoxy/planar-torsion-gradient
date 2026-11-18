module

public import Torsion.CauchyConformalGeometry.Inverse
public import Torsion.SpectralNormalization

@[expose] public section

/-! # Reflection symmetry of the Cauchy image -/

noncomputable section
open Set MeasureTheory

namespace Torsion.Spectral

/-- The Cauchy map intertwines reflection in the imaginary axis on its
parameter plane and its image. This uses only evenness of the height. -/
theorem cauchy_reflection (φ : ℝ → ℝ) (z : ℂ) :
    cauchy φ (-star z) = -star (cauchy φ z) := by
  let k (s : ℝ) : ℂ := (height φ s : ℂ) / (z - (s : ℂ))
  have hmirror : (∫ s in Icc (-1 : ℝ) 1, k (-s)) = ∫ s in Icc (-1 : ℝ) 1, k s := by
    simp only [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := k) (a := (-1 : ℝ)) (b := (1 : ℝ)))
  have hkernel (s : ℝ) :
      (height φ s : ℂ) / (-star z - (s : ℂ)) = -star (k (-s)) := by
    simp only [k, height_even φ s, Complex.ofReal_neg, Complex.star_def, map_div₀, map_add,
      Complex.conj_ofReal, sub_neg_eq_add]
    rw [show -(starRingEnd ℂ) z - (s : ℂ) = -((starRingEnd ℂ) z + (s : ℂ)) by ring, div_neg]
  have hint : (∫ s in Icc (-1 : ℝ) 1, (height φ s : ℂ) / (-star z - (s : ℂ))) =
      -star (∫ s in Icc (-1 : ℝ) 1, k s) := by
    calc
      _ = ∫ s in Icc (-1 : ℝ) 1, -star (k (-s)) :=
        setIntegral_congr_fun measurableSet_Icc (fun s _ => hkernel s)
      _ = _ := by rw [integral_neg, Complex.star_def, integral_conj, hmirror]
  unfold cauchy
  rw [hint]
  change -(Real.pi : ℂ)⁻¹ * -star (∫ s in Icc (-1 : ℝ) 1, k s) =
    -star (-(Real.pi : ℂ)⁻¹ * (∫ s in Icc (-1 : ℝ) 1, k s))
  simp

/-- The canonical domain, including its interior, is symmetric in the
imaginary axis. The same holds for any profile in this construction. -/
theorem cauchyImage_reflection_iff (φ : ℝ → ℝ) (w : ℂ) :
    -star w ∈ cauchyImage φ ↔ w ∈ cauchyImage φ := by
  have hreflect (v : ℂ) (hv : v ∈ cauchyImage φ) : -star v ∈ cauchyImage φ := by
    obtain ⟨z, hz, rfl⟩ := hv
    refine ⟨-star z, ?_, cauchy_reflection φ z⟩
    simpa only [upperHalfPlane, mem_ofPred_eq, Complex.neg_im, Complex.star_def,
      Complex.conj_im, neg_neg] using hz
  exact ⟨fun h => by simpa using hreflect (-star w) h, hreflect w⟩

/-- Reflection symmetry is preserved by the real scale factor giving
the paper's unit-area maximizing domain. -/
theorem normalizedImage_reflection_iff (a : ℝ) (φ : ℝ → ℝ) (w : ℂ) :
    -star w ∈ normalizedImage a φ ↔ w ∈ normalizedImage a φ := by
  have hreflect (v : ℂ) (hv : v ∈ normalizedImage a φ) : -star v ∈ normalizedImage a φ := by
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨-star u, (cauchyImage_reflection_iff φ u).2 hu, ?_⟩
    simp
  exact ⟨fun h => by simpa using hreflect (-star w) h, hreflect w⟩

end Torsion.Spectral

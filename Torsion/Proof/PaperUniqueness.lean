module

public import Torsion.Proof.PaperFrameLimit
public import Torsion.Proof.PaperMaximizerApproximation
public import Torsion.Proof.PaperSimilarity

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Classification of all maximizing domains

The supporting frames of nearly maximizing observations have a convergent
subsequence. In the limiting frame the original area-one domain agrees with
the normalized Cauchy image. Scaling gives the classification at every area.
-/

noncomputable section
open Set

namespace Torsion

open Spectral

/-- Any area-one maximizer is a rigid image of the constructed domain. -/
theorem second_area_one_maximizer_rigidity (D : ConvexDomain) (ha : D.area = 1)
    (hg : torsionTheory.G D = ENNReal.ofReal
      (spectralConstant secondEigenvalue secondEigenfunction)) :
    ∃ (p : Plane) (U : Plane ≃ₗᵢ[ℝ] Plane),
      D.carrier = (fun z => p + U z) '' normalizedImage secondEigenvalue secondEigenfunction := by
  obtain ⟨K, hK, harea, _⟩ := second_exact_value.2
  obtain ⟨p, n, hn, E, hp, hsub, hvol⟩ := exists_areaOne_maximizer_outer_sequence D ha hg
  rw [← hK] at hvol
  obtain ⟨a, _, v, hv, heq⟩ :=
    D.exists_inNormalFrame_eq_of_outer_limit K (ha.trans harea.symm) p n hn E hp hsub hvol
  let U := normalFrame v hv
  refine ⟨a, U, ?_⟩
  rw [← hK, ← heq]
  ext z
  constructor
  · intro hz
    refine ⟨U.symm (z - a), ?_, ?_⟩
    · apply (D.mem_inNormalFrame a v _ hv).mpr
      change U (U.symm (z - a)) + a ∈ D.carrier
      simpa only [U.apply_symm_apply, sub_add_cancel] using hz
    · change a + U (U.symm (z - a)) = z
      rw [U.apply_symm_apply, add_comm, sub_add_cancel]
  · rintro ⟨w, hw, rfl⟩
    simpa only [add_comm] using (D.mem_inNormalFrame a v _ hv).mp hw

/-- Theorem 1.2. Equality holds exactly on the similarity orbit of the
normalized second-eigenfunction Cauchy image, at every positive area. -/
theorem second_sharp_equality_iff_similarity (D : ConvexDomain) :
    torsionTheory.G D = ENNReal.ofReal
        (spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt D.area) ↔
      ∃ (p : Plane) (s : ℝ), 0 < s ∧ ∃ (U : Plane ≃ₗᵢ[ℝ] Plane),
        D.carrier = (fun z => p + s • U z) ''
          normalizedImage secondEigenvalue secondEigenfunction := by
  constructor
  · exact second_similarity_of_area_one_rigidity second_area_one_maximizer_rigidity D
  · rintro ⟨p, s, hs, U, h⟩
    exact second_sharp_equality_of_similarity D p s hs U h

end Torsion

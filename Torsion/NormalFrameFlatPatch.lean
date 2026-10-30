module

public import Torsion.NormalFrame
public import Torsion.SupportedConvexFlatHullUniform

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Uniform interior balls and flat outer patches in supporting normal frames -/

noncomputable section
open Set Metric
namespace Torsion
namespace ConvexDomain

/-- The actual interior ball is preserved by translation and the orthogonal
support frame, with exactly the physical support height and norm bounds. -/
theorem inNormalFrame_inball_bounds (D : ConvexDomain) (p n a : Plane)
    (hn : ‖n‖ = 1) {h M : ℝ} (hh : 0 < h)
    (hball : ball a h ⊆ D.carrier) (hheight : h ≤ inner (𝕜 := ℝ) n (a - p))
    (hnorm : ‖a - p‖ ≤ M) :
    let a' := (normalFrame n hn).symm (a - p)
    a' ∈ (D.inNormalFrame p n hn).carrier ∧
      ball a' h ⊆ (D.inNormalFrame p n hn).carrier ∧ h ≤ a'.im ∧ ‖a'‖ ≤ M := by
  dsimp only
  have heq : normalFrame n hn ((normalFrame n hn).symm (a - p)) + p = a := by
    rw [LinearIsometryEquiv.apply_symm_apply, sub_add_cancel]
  have hball' : ball ((normalFrame n hn).symm (a - p)) h ⊆
      (D.inNormalFrame p n hn).carrier := by
    intro z hz
    rw [mem_inNormalFrame]
    apply hball
    rw [mem_ball] at hz ⊢
    calc
      dist (normalFrame n hn z + p) a =
          dist (normalFrame n hn z + p)
            (normalFrame n hn ((normalFrame n hn).symm (a - p)) + p) := by rw [heq]
      _ = dist z ((normalFrame n hn).symm (a - p)) := by
        rw [dist_add_right, LinearIsometryEquiv.dist_map]
      _ < h := hz
  refine ⟨hball' (mem_ball_self hh), hball', ?_, ?_⟩
  · rwa [normalFrame_symm_im]
  · simpa only [LinearIsometryEquiv.norm_map] using hnorm

/-- The quantitative flat patch is uniform over all supporting frames
satisfying the same physical inball and distance bounds. -/
theorem flatOuterHull_inNormalFrame_uniform_patch (D : ConvexDomain) (p n a : Plane)
    (hn : ‖n‖ = 1) {r h M : ℝ} (hr : 0 < r) (hh : 0 < h) (hM : 0 ≤ M)
    (hball : ball a h ⊆ D.carrier)
    (hheight : h ≤ inner (𝕜 := ℝ) n (a - p)) (hnorm : ‖a - p‖ ≤ M)
    (hsupport : ∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) n (z - p)) :
    flatOuterHull (D.inNormalFrame p n hn).carrier r ∩
        ball (0 : Plane) (flatHullPatchRadius r h M) =
      upperHalfPlane ∩ ball (0 : Plane) (flatHullPatchRadius r h M) := by
  obtain ⟨ha', _, hheight', hnorm'⟩ := D.inNormalFrame_inball_bounds p n a hn hh hball hheight hnorm
  exact flatOuterHull_inter_ball_of_point_bounds (D.inNormalFrame p n hn).isOpen
    (D.inNormalFrame_subset_upper p n hn hsupport) ha' hr hh hM hheight' hnorm'

end ConvexDomain
end Torsion

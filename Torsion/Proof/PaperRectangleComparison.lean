module

public import Torsion.Proof.PaperBoundaryComparison
public import Torsion.Proof.PaperRectangleBarrier

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # A loss at the top of a rectangle bounds the normal quotient at its base -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace Torsion

/-- A Lipschitz zero extension above a supporting line is bounded by its
Lipschitz constant times the height above that line. -/
theorem le_height_of_supporting_line {D : Set Plane} {U : Plane → ℝ}
    (hhalf : D ⊆ upperHalfPlane) (hzero : ∀ z ∉ D, U z = 0)
    (L : ℝ≥0) (hlip : LipschitzWith L U) (z : Plane) (hy : 0 ≤ z.im) :
    U z ≤ L * z.im := by
  have hout : (z.re : Plane) ∉ D := by
    intro h
    have hy : 0 < ((z.re : ℝ) : Plane).im := hhalf h
    simpa only [Complex.ofReal_im, lt_self_iff_false] using hy
  have hdiff : z - (z.re : Plane) = (z.im : Plane) * Complex.I := by
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using (Complex.re_add_im z).symm)
  calc
    U z ≤ |U z| := le_abs_self _
    _ = dist (U z) (U (z.re : Plane)) := by rw [hzero _ hout, Real.dist_eq, sub_zero]
    _ ≤ L * dist z (z.re : Plane) := hlip.dist_le_mul _ _
    _ = L * z.im := by
      rw [dist_eq_norm, hdiff, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]

/-- For a domain above the horizontal supporting line, a uniform loss in
the linear Lipschitz bound on the roof of a rectangle forces a definite
loss in the normal quotient at the bottom, up to the Poisson forcing. -/
theorem supporting_rectangle_quotient_le (D : ConvexDomain) {U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D.carrier U g) (hhalf : D.carrier ⊆ upperHalfPlane)
    (hs : ContDiffOn ℝ ∞ U D.carrier) (hg : g =ᵐ[volume.restrict D.carrier] gradient U)
    (hzero : ∀ z ∉ D.carrier, U z = 0) (L : ℝ≥0) (hlip : LipschitzWith L U)
    {R δ η : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hη : 0 < η) (hηL : η ≤ L)
    (hroof : ∀ z : Plane, |z.re| ≤ δ*R → z.im = R → U z ≤ (L-η)*R)
    {t : ℝ} (ht : 0 < t) (htR : t < R) (hin : (t : Plane)*Complex.I ∈ D.carrier) :
    U ((t : Plane)*Complex.I)/t ≤ L - η / Real.cosh (Real.pi/(2*δ)) + R/2 := by
  let W : Set Plane := {z | |z.re| < δ*R ∧ z.im < R}
  let S := D.carrier ∩ W
  have hopen : IsOpen S := D.isOpen.inter ((isOpen_lt Complex.continuous_re.abs continuous_const).inter
    (isOpen_lt Complex.continuous_im continuous_const))
  have hSD : S ⊆ D.carrier := inter_subset_left
  have hcl : closure S ⊆ {z : Plane | |z.re| ≤ δ*R ∧ 0 ≤ z.im ∧ z.im ≤ R} := by
    apply closure_minimal
    · intro z hz
      exact ⟨hz.2.1.le, (show 0 < z.im from hhalf hz.1).le, hz.2.2.le⟩
    · exact (isClosed_le Complex.continuous_re.abs continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
         (isClosed_le Complex.continuous_im continuous_const))
  let H := rectangleBarrier R δ η
  have hfront (z : Plane) (hz : z ∈ frontier S) :
      U z + H z ≤ slabTorsionBarrier 0 (2*L+R) z := by
    obtain ⟨hx, hy, hy'⟩ := hcl (frontier_subset_closure hz)
    have hbar : H z ≤ η*z.im := rectangleBarrier_le_height hR hδ hη.le hy hy'
    have hslab : (L : ℝ)*z.im ≤ slabTorsionBarrier 0 (2*L+R) z := by
      dsimp [slabTorsionBarrier]
      nlinarith [mul_nonneg hy (sub_nonneg.mpr hy')]
    apply le_trans _ hslab
    by_cases hzD : z ∈ D.carrier
    · have hnS : z ∉ S := (hopen.frontier_eq ▸ hz).2
      by_cases htop : z.im = R
      · have hb := hroof z hx htop
        rw [htop] at hbar ⊢
        linarith
      · have hside : |z.re| = δ * R := le_antisymm hx (le_of_not_gt
          (fun hx' => hnS ⟨hzD, hx', lt_of_le_of_ne hy' htop⟩))
        have halts : z.re = δ*R ∨ z.re = -(δ*R) := by
          by_cases h : 0 ≤ z.re
          · exact Or.inl (by rwa [abs_of_nonneg h] at hside)
          · exact Or.inr (by rw [abs_of_neg (lt_of_not_ge h)] at hside; linarith)
        rw [show H z = 0 from rectangleBarrier_eq_zero_of_side hR hδ η halts, add_zero]
        exact le_height_of_supporting_line hhalf hzero L hlip z hy
    · rw [hzero z hzD, zero_add]
      exact hbar.trans (mul_le_mul_of_nonneg_right hηL hy)
  have hcomp := hu.le_slab_sub_harmonic_on D.isOpen hopen (D.bounded.subset hSD) hSD
    hlip.continuous hs hg (2*L+R) (rectangleBarrier_contDiff R δ η)
    (rectangleBarrier_laplacian R δ η) hfront
  let z : Plane := (t : Plane)*Complex.I
  have hyz : z.im = t := by simp [z]
  have hxz : z.re = 0 := by simp [z]
  have hz : z ∈ S := ⟨hin, by rw [hxz, abs_zero]; exact mul_pos hδ hR, by rwa [hyz]⟩
  have h := hcomp z hz
  have hlo := rectangleBarrier_axis_lower hR hδ hη.le ht.le
  change η / Real.cosh (Real.pi / (2 * δ)) * t ≤ rectangleBarrier R δ η z at hlo
  rw [slabTorsionBarrier, hyz] at h
  apply (div_le_iff₀ ht).mpr
  change U z ≤ _
  nlinarith [sq_nonneg t]

end Torsion

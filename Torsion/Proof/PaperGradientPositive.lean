module

public import Torsion.SobolevCore
public import Torsion.CanonicalUniversal
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section

/-! # Strict positivity of the torsion-gradient objective -/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace Torsion

/-- Testing the unit forcing against an interior bump excludes a vanishing
weak gradient on every admissible domain. -/
theorem DirichletTheory.G_pos (T : DirichletTheory) (D : ConvexDomain) : 0 < T.G D := by
  apply pos_iff_ne_zero.mpr
  intro h
  let u := T.solution D
  have hg : u.weakGradient =ᵐ[volume.restrict D.carrier] 0 :=
    (eLpNorm_eq_zero_iff (by norm_num : (∞ : ℝ≥0∞) ≠ 0)).mp h
  obtain ⟨x, hx⟩ := D.nonempty
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp D.isOpen x hx
  let f : ContDiffBump x :=
    { rIn := r / 4, rOut := r / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hf : IsTest D.carrier (f : Plane → ℝ) := by
    refine ⟨f.contDiff, f.hasCompactSupport, ?_⟩
    rw [f.tsupport_eq]
    exact (closedBall_subset_ball (by change r / 2 < r; linarith)).trans hsub
  have heq := u.weakEquation.2 f (gradient (f : Plane → ℝ)) hf.memH10
  have hload : (∫ z in D.carrier, f z) = ∫ z, f z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz =>
      image_eq_zero_of_notMem_tsupport (fun hzt => hz (hf.2.2 hzt)))
  have hpair : (∫ z in D.carrier, inner (𝕜 := ℝ) (u.weakGradient z)
      (gradient (f : Plane → ℝ) z)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hg] with z hz
    simp only [Pi.zero_apply] at hz
    simp [hz]
  rw [hload, hpair] at heq
  exact (f.integral_pos (μ := volume)).ne' heq.symm

/-- The real-valued objective is strictly positive as well: its extended
value is finite by the sharp bound. -/
theorem DirichletTheory.G_toReal_pos (T : DirichletTheory) (D : ConvexDomain) :
    0 < (T.G D).toReal :=
  ENNReal.toReal_pos (T.G_pos D).ne'
    (lt_of_le_of_lt (T.G_le_second_spectral_bound D) ENNReal.ofReal_lt_top).ne

end Torsion

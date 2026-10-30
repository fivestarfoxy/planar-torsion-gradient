import Torsion.Definitions
import Torsion.SobolevAdd
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.Tactic

/-!
# A proved planar Poincaré estimate

The estimate is derived from mathlib's Gagliardo--Nirenberg--Sobolev theorem
in real dimension two and Hölder's inequality on a bounded containing domain.
The second theorem passes the estimate to the actual H¹₀ closure used here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
namespace Torsion

/-- A finite, explicit coefficient for the planar Poincaré estimate. -/
def poincareCoefficient (D : ConvexDomain) : ℝ≥0∞ :=
  (eLpNormLESNormFDerivOneConst (E := Plane) volume 2 : ℝ≥0∞) *
    (volume D.carrier) ^ (1 / 2 : ℝ)

theorem poincareCoefficient_ne_top (D : ConvexDomain) : poincareCoefficient D ≠ ⊤ := by
  unfold poincareCoefficient
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) D.bounded.measure_lt_top.ne)

/-- The gradient and real Fréchet derivative have identical norms. -/
theorem norm_gradient_eq_fderiv (f : Plane → ℝ) (x : Plane) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

/-- Actual smooth-test estimate, with Lebesgue measure and physical gradient. -/
theorem IsTest.poincare {D : ConvexDomain} {f : Plane → ℝ}
    (hf : IsTest D.carrier f) :
    eLpNorm f 2 volume ≤ poincareCoefficient D * eLpNorm (gradient f) 2 volume := by
  have hc : ContDiff ℝ 1 f := hf.1.of_le (by simp)
  have hfd : AEStronglyMeasurable (fderiv ℝ f) volume :=
    (hc.continuous_fderiv le_rfl).aestronglyMeasurable
  have hs : Function.support (fderiv ℝ f) ⊆ D.carrier :=
    (support_fderiv_subset ℝ).trans hf.2.2
  have hGN : eLpNorm f 2 volume ≤
      (eLpNormLESNormFDerivOneConst (E := Plane) volume 2 : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 1 volume := by
    apply eLpNorm_le_eLpNorm_fderiv_one volume hc hf.2.1
    change (↑(Module.finrank ℝ ℂ) : ℝ≥0).HolderConjugate 2
    rw [Complex.finrank_real_complex]
    rw [← NNReal.holderConjugate_coe_iff]
    norm_num [Real.holderConjugate_iff]
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict D.carrier) (f := fderiv ℝ f)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hfd.restrict
  have hrestrict (p : ℝ≥0∞) :
      eLpNorm (fderiv ℝ f) p (volume.restrict D.carrier) =
        eLpNorm (fderiv ℝ f) p volume :=
    eLpNorm_restrict_eq_of_support_subset (f := fderiv ℝ f) hs
  simp only [hrestrict, Measure.restrict_apply_univ] at hH
  norm_num at hH
  have hnorm : eLpNorm (fderiv ℝ f) 2 volume = eLpNorm (gradient f) 2 volume := by
    apply eLpNorm_congr_norm_ae
    exact ae_of_all _ fun x => (norm_gradient_eq_fderiv f x).symm
  calc
    eLpNorm f 2 volume ≤ _ := hGN
    _ ≤ (eLpNormLESNormFDerivOneConst (E := Plane) volume 2 : ℝ≥0∞) *
        (eLpNorm (fderiv ℝ f) 2 volume * (volume D.carrier) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_left' hH _
    _ = poincareCoefficient D * eLpNorm (gradient f) 2 volume := by
      rw [hnorm]
      unfold poincareCoefficient
      ring

/-- Passing the proved estimate to the simultaneous L² graph closure.
This is the Poincaré inequality for the actual `MemH10` predicate. -/
theorem MemH10.poincare {D : ConvexDomain} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D.carrier u g) :
    eLpNorm u 2 volume ≤ poincareCoefficient D * eLpNorm g 2 volume := by
  rcases hu with ⟨hu, hg, f, hf, hfu, hfg⟩
  have hbound (n : ℕ) : eLpNorm u 2 volume ≤
      eLpNorm (fun x => f n x - u x) 2 volume +
        poincareCoefficient D *
          (eLpNorm (fun x => gradient (f n) x - g x) 2 volume + eLpNorm g 2 volume) := by
    have hval : eLpNorm u 2 volume ≤
        eLpNorm (fun x => f n x - u x) 2 volume + eLpNorm (f n) 2 volume := by
      have h := eLpNorm_add_le (hu.1.sub (hf n).1.continuous.aestronglyMeasurable)
        (hf n).1.continuous.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hsum : (u - f n) + f n = u := by ext x; simp
      rw [hsum, eLpNorm_sub_comm] at h
      exact h
    have hgrad : eLpNorm (gradient (f n)) 2 volume ≤
        eLpNorm (fun x => gradient (f n) x - g x) 2 volume + eLpNorm g 2 volume := by
      have h := eLpNorm_add_le ((hf n).continuous_gradient.aestronglyMeasurable.sub hg.1)
        hg.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hsum : (gradient (f n) - g) + g = gradient (f n) := by ext x; simp
      rwa [hsum] at h
    exact hval.trans (add_le_add_left
      ((hf n).poincare.trans (mul_le_mul_left' hgrad _)) _)
  have hlim := hfu.add (ENNReal.Tendsto.const_mul
    (hfg.add (tendsto_const_nhds (x := eLpNorm g 2 volume)))
    (Or.inr (poincareCoefficient_ne_top D)))
  have h := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound
  simpa only [zero_add] using h

/-- A positive finite real Poincaré constant, convenient for coercivity. -/
theorem exists_poincare_constant (D : ConvexDomain) :
    ∃ K : ℝ, 0 < K ∧ ∀ (u : Plane → ℝ) (g : Plane → Plane),
      MemH10 D.carrier u g → eLpNorm u 2 volume ≤ ENNReal.ofReal K * eLpNorm g 2 volume := by
  refine ⟨(poincareCoefficient D).toReal + 1, by positivity, ?_⟩
  intro u g hu
  apply hu.poincare.trans
  apply mul_le_mul_right'
  calc
    poincareCoefficient D = ENNReal.ofReal (poincareCoefficient D).toReal :=
      (ENNReal.ofReal_toReal (poincareCoefficient_ne_top D)).symm
    _ ≤ ENNReal.ofReal ((poincareCoefficient D).toReal + 1) :=
      ENNReal.ofReal_le_ofReal (by linarith)

end Torsion
end

import Torsion.SobolevCore
import Torsion.Sobolev
import Torsion.BoundedDomains
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# Multiplication by smooth compact cutoffs in the actual Sobolev closure

Multiplying the defining approximants by a compact cutoff localizes them
inside the cutoff domain. Both value and gradient convergence are proved in
L² using bounded-multiplier estimates; no weak chain rule is assumed.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Torsion

theorem gradient_mul_of_differentiable {f k : Plane → ℝ}
    (hf : Differentiable ℝ f) (hk : Differentiable ℝ k) (x : Plane) :
    gradient (fun y => f y * k y) x = f x • gradient k x + k x • gradient f x := by
  unfold gradient
  rw [fderiv_mul (hf x) (hk x)]
  simp only [map_add, map_smul]

/-- A smooth test can localize another smooth function, even if its original
support is in a different domain. -/
theorem IsTest.mul_left {D : Set Plane} {f k : Plane → ℝ}
    (hf : IsTest D f) (hk : ContDiff ℝ ∞ k) :
    IsTest D (fun x => f x * k x) := by
  refine ⟨hf.1.mul hk, hf.2.1.mul_right, ?_⟩
  exact tsupport_mul_subset_left.trans hf.2.2

private theorem tendsto_eLpNorm_fixed_smul_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : Plane → ℝ} {f : ℕ → Plane → E}
    (ha : MemLp a ∞ volume) (hf : ∀ n, AEStronglyMeasurable (f n) volume)
    (hlim : Tendsto (fun n => eLpNorm (f n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a x • f n x) 2 volume) atTop (𝓝 0) := by
  have hbound (n : ℕ) := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 (hf n) a
  have hlim' := ENNReal.Tendsto.const_mul hlim (Or.inr ha.eLpNorm_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hlim') (fun _ => zero_le _) hbound

private theorem tendsto_eLpNorm_smul_fixed_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Plane → E} {a : ℕ → Plane → ℝ}
    (hg : MemLp g ∞ volume) (ha : ∀ n, AEStronglyMeasurable (a n) volume)
    (hlim : Tendsto (fun n => eLpNorm (a n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x • g x) 2 volume) atTop (𝓝 0) := by
  have hbound (n : ℕ) := eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top 2 g (ha n)
  have hlim' := ENNReal.Tendsto.mul_const hlim (Or.inr hg.eLpNorm_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hlim') (fun _ => zero_le _) hbound

/-- The product-rule graph of a compact cutoff times an H¹₀ function belongs
to the cutoff domain's H¹₀ closure. -/
theorem MemH10.mul_test_inter {D E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 E u g) {η : Plane → ℝ} (hη : IsTest D η) :
    MemH10 (E ∩ D) (fun x => η x * u x)
      (fun x => η x • g x + u x • gradient η x) := by
  rcases hu with ⟨hu, hg, f, hf, hfu, hfg⟩
  have hηm : MemLp η ∞ volume := hη.memLp_value
  have hηg : MemLp (gradient η) ∞ volume := hη.memLp_gradient
  have htest (n : ℕ) : IsTest (E ∩ D) (fun x => η x * f n x) := by
    have ht := hη.mul_left (hf n).1
    exact ⟨ht.1, ht.2.1, subset_inter
      (tsupport_mul_subset_right.trans (hf n).2.2) ht.2.2⟩
  refine ⟨?_, ?_, (fun n x => η x * f n x), htest, ?_, ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using hu.smul hηm
  · exact (hg.smul hηm).add (hηg.smul hu)
  · have h := tendsto_eLpNorm_fixed_smul_zero hηm
      (fun n => (hf n).1.continuous.aestronglyMeasurable.sub hu.1) hfu
    convert h using 1
    funext n
    congr 1
    ext x
    simp only [smul_eq_mul, Pi.sub_apply]
    ring
  · have hA := tendsto_eLpNorm_fixed_smul_zero hηm
      (fun n => (hf n).continuous_gradient.aestronglyMeasurable.sub hg.1) hfg
    have hB := tendsto_eLpNorm_smul_fixed_zero hηg
      (fun n => (hf n).1.continuous.aestronglyMeasurable.sub hu.1) hfu
    have hbound (n : ℕ) := eLpNorm_add_le
      (hηm.1.smul ((hf n).continuous_gradient.aestronglyMeasurable.sub hg.1))
      (((hf n).1.continuous.aestronglyMeasurable.sub hu.1).smul hηg.1)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hlim : Tendsto (fun n => eLpNorm
        (fun x => η x • (gradient (f n) x - g x) + (f n x - u x) • gradient η x)
        2 volume) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using hA.add hB) (fun _ => zero_le _) hbound
    convert hlim using 1
    funext n
    congr 1
    ext x
    rw [gradient_mul_of_differentiable (hη.1.differentiable (by simp))
      ((hf n).1.differentiable (by simp))]
    simp only [Pi.sub_apply, smul_sub, sub_smul]
    abel

/-- The usual localization statement, retaining its earlier interface. -/
theorem MemH10.mul_test {D E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 E u g) {η : Plane → ℝ} (hη : IsTest D η) :
    MemH10 D (fun x => η x * u x)
      (fun x => η x • g x + u x • gradient η x) :=
  (hu.mul_test_inter hη).mono inter_subset_right

end Torsion
end

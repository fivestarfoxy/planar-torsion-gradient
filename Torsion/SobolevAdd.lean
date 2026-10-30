module

public import Torsion.Definitions
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

/-! # Addition in the concrete zero-trace Sobolev graph closure -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- The pointwise gradient addition rule for differentiable planar functions. -/
theorem gradient_add_of_differentiable {f g : Plane → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Plane) :
    gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
  simp only [gradient, fderiv_fun_add (hf x) (hg x), map_add]

/-- Smooth compactly supported test functions in a fixed domain form an additive group. -/
theorem IsTest.add {D : Set Plane} {f g : Plane → ℝ}
    (hf : IsTest D f) (hg : IsTest D g) : IsTest D (fun x => f x + g x) := by
  exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    (tsupport_add f g).trans (union_subset hf.2.2 hg.2.2)⟩

/-- Smooth planar functions have continuous gradients. -/
theorem IsTest.continuous_gradient {D : Set Plane} {f : Plane → ℝ}
    (hf : IsTest D f) : Continuous (gradient f) := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp
    (hf.1.continuous_fderiv (by simp))

private theorem tendsto_eLpNorm_add_zero
    {E : Type*} [NormedAddCommGroup E] {f g : ℕ → Plane → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) volume)
    (hg : ∀ n, AEStronglyMeasurable (g n) volume)
    (hflim : Tendsto (fun n => eLpNorm (f n) 2 volume) atTop (𝓝 0))
    (hglim : Tendsto (fun n => eLpNorm (g n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => f n x + g n x) 2 volume) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hflim.add hglim)
  · intro n
    exact zero_le
  · intro n
    exact eLpNorm_add_le (by norm_num)

/-- Addition preserves `MemH10`, proved using the sums of the supplied smooth
compactly supported approximants in both the value and gradient coordinates. -/
theorem MemH10.add {D : Set Plane} {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : MemH10 D u g) (hv : MemH10 D v h) :
    MemH10 D (fun x => u x + v x) (fun x => g x + h x) := by
  rcases hu with ⟨hu, hg, f, hf, hfu, hfg⟩
  rcases hv with ⟨hv, hh, k, hk, hkv, hkh⟩
  refine ⟨hu.add hv, hg.add hh, (fun n x => f n x + k n x),
    (fun n => (hf n).add (hk n)), ?_, ?_⟩
  · have hlim := tendsto_eLpNorm_add_zero
      (fun n => ((hf n).1.continuous.aestronglyMeasurable).sub hu.aestronglyMeasurable)
      (fun n => ((hk n).1.continuous.aestronglyMeasurable).sub hv.aestronglyMeasurable) hfu hkv
    convert hlim using 1
    funext n
    congr 1
    funext x
    simp only [Pi.sub_apply]
    abel
  · have hlim := tendsto_eLpNorm_add_zero
      (fun n => ((hf n).continuous_gradient.aestronglyMeasurable).sub hg.aestronglyMeasurable)
      (fun n => ((hk n).continuous_gradient.aestronglyMeasurable).sub hh.aestronglyMeasurable) hfg hkh
    convert hlim using 1
    funext n
    congr 1
    funext x
    rw [gradient_add_of_differentiable
      ((hf n).1.differentiable (by simp)) ((hk n).1.differentiable (by simp))]
    simp only [Pi.sub_apply]
    abel

end Torsion

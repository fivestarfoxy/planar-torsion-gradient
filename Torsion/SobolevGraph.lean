import Torsion.SobolevCore
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Module.Basic

/-!
# A complete closed subspace realizing the concrete `MemH10` predicate

The smooth core is a submodule of the product of value and gradient L² spaces.
Its topological closure is complete, and membership is equivalent to the actual
simultaneous approximation predicate in `Definitions.lean`.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Value/gradient pairs in the ambient product of L² spaces. -/
abbrev SobolevPair := Lp ℝ 2 (volume : Measure Plane) × Lp Plane 2 (volume : Measure Plane)

/-- The concrete L² graph point of a smooth compactly supported test function. -/
def IsTest.graph {D : Set Plane} {f : Plane → ℝ} (hf : IsTest D f) : SobolevPair :=
  ⟨hf.memLp_value.toLp f, hf.memLp_gradient.toLp (gradient f)⟩

/-- The test graph map respects addition. -/
theorem IsTest.graph_add {D : Set Plane} {f g : Plane → ℝ}
    (hf : IsTest D f) (hg : IsTest D g) :
    (hf.add hg).graph = hf.graph + hg.graph := by
  apply Prod.ext
  · exact MemLp.toLp_add hf.memLp_value hg.memLp_value
  · change (hf.add hg).memLp_gradient.toLp (gradient (fun x => f x + g x)) =
      hf.memLp_gradient.toLp (gradient f) + hg.memLp_gradient.toLp (gradient g)
    rw [← MemLp.toLp_add hf.memLp_gradient hg.memLp_gradient]
    apply (MemLp.toLp_eq_toLp_iff _ _).mpr
    exact Eventually.of_forall (fun x => gradient_add_of_differentiable
      (hf.1.differentiable (by simp)) (hg.1.differentiable (by simp)) x)

/-- The test graph map respects real scalar multiplication. -/
theorem IsTest.graph_const_smul {D : Set Plane} {f : Plane → ℝ}
    (hf : IsTest D f) (c : ℝ) : (hf.const_smul c).graph = c • hf.graph := by
  apply Prod.ext
  · exact MemLp.toLp_const_smul c hf.memLp_value
  · change (hf.const_smul c).memLp_gradient.toLp (gradient (fun x => c • f x)) =
      c • hf.memLp_gradient.toLp (gradient f)
    rw [← MemLp.toLp_const_smul c hf.memLp_gradient]
    apply (MemLp.toLp_eq_toLp_iff _ _).mpr
    exact Eventually.of_forall (fun x => gradient_real_const_smul
      (hf.1.differentiable (by simp)) c x)

/-- The graph of the zero test function is the zero ambient pair. -/
theorem isTest_zero_graph (D : Set Plane) : (isTest_zero D).graph = 0 := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(isTest_zero D).memLp_value.coeFn_toLp] with x hx
    simpa [IsTest.graph] using hx
  · apply Lp.ext
    filter_upwards [(isTest_zero D).memLp_gradient.coeFn_toLp] with x hx
    simpa [IsTest.graph, gradient_const] using hx

/-- The smooth test graphs, as an actual real linear subspace. -/
def testGraphSubmodule (D : Set Plane) : Submodule ℝ SobolevPair where
  carrier := {p | ∃ f : Plane → ℝ, ∃ hf : IsTest D f, hf.graph = p}
  zero_mem' := ⟨_, isTest_zero D, isTest_zero_graph D⟩
  add_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨_, hf.add hg, hf.graph_add hg⟩
  smul_mem' := by
    rintro c a ⟨f, hf, rfl⟩
    exact ⟨_, hf.const_smul c, hf.graph_const_smul c⟩

/-- A complete closed subspace of the value/gradient L² product. -/
def H10Graph (D : Set Plane) : Submodule ℝ SobolevPair :=
  (testGraphSubmodule D).topologicalClosure

/-- The graph closure is closed in the ambient L² product. -/
theorem isClosed_H10Graph (D : Set Plane) : IsClosed (H10Graph D : Set SobolevPair) :=
  Submodule.isClosed_topologicalClosure _

/-- Graph closure membership is exactly the simultaneous smooth approximation
used in the original definition, with no new analytic assumptions. -/
theorem memH10_iff_mem_H10Graph {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume) :
    MemH10 D u g ↔ (hu.toLp u, hg.toLp g) ∈ H10Graph D := by
  change MemH10 D u g ↔ (hu.toLp u, hg.toLp g) ∈ closure (testGraphSubmodule D : Set SobolevPair)
  constructor
  · rintro ⟨_, _, f, hf, hfu, hfg⟩
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun n => (hf n).graph, (fun n => ⟨f n, hf n, rfl⟩), ?_⟩
    apply Tendsto.prodMk_nhds
    · apply tendsto_iff_edist_tendsto_0.mpr
      simpa only [IsTest.graph, Lp.edist_toLp_toLp] using hfu
    · apply tendsto_iff_edist_tendsto_0.mpr
      simpa only [IsTest.graph, Lp.edist_toLp_toLp] using hfg
  · intro hmem
    obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
    choose f hf heq using hp
    have hlim' : Tendsto (fun n => (hf n).graph) atTop (𝓝 (hu.toLp u, hg.toLp g)) := by
      simpa only [heq] using hlim
    refine ⟨hu, hg, f, hf, ?_, ?_⟩
    · have hl := tendsto_iff_edist_tendsto_0.mp hlim'.fst_nhds
      simpa only [IsTest.graph, Lp.edist_toLp_toLp] using hl
    · have hl := tendsto_iff_edist_tendsto_0.mp hlim'.snd_nhds
      simpa only [IsTest.graph, Lp.edist_toLp_toLp] using hl

/-- The actual Sobolev graph is closed under simultaneous L² limits. -/
theorem MemH10.of_tendsto {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    {uₙ : ℕ → Plane → ℝ} {gₙ : ℕ → Plane → Plane}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hseq : ∀ n, MemH10 D (uₙ n) (gₙ n))
    (hval : Tendsto (fun n => eLpNorm (fun x => uₙ n x - u x) 2 volume) atTop (𝓝 0))
    (hgrad : Tendsto (fun n => eLpNorm (fun x => gₙ n x - g x) 2 volume) atTop (𝓝 0)) :
    MemH10 D u g := by
  apply (memH10_iff_mem_H10Graph hu hg).mpr
  have hv : Tendsto (fun n => (hseq n).1.toLp (uₙ n)) atTop (𝓝 (hu.toLp u)) := by
    apply tendsto_iff_edist_tendsto_0.mpr
    simpa only [Lp.edist_toLp_toLp] using hval
  have hh : Tendsto (fun n => (hseq n).2.1.toLp (gₙ n)) atTop (𝓝 (hg.toLp g)) := by
    apply tendsto_iff_edist_tendsto_0.mpr
    simpa only [Lp.edist_toLp_toLp] using hgrad
  apply (isClosed_H10Graph D).mem_of_tendsto (hv.prodMk_nhds hh)
  exact Eventually.of_forall (fun n =>
    (memH10_iff_mem_H10Graph (hseq n).1 (hseq n).2.1).mp (hseq n))

/-- Every point in the closed graph provides actual representatives satisfying
`MemH10`, as needed to extract a weak solution from a variational construction. -/
theorem H10Graph.memH10_coe {D : Set Plane} (p : H10Graph D) :
    MemH10 D (p.1.1 : Plane → ℝ) (p.1.2 : Plane → Plane) := by
  apply (memH10_iff_mem_H10Graph (Lp.memLp p.1.1) (Lp.memLp p.1.2)).mpr
  simpa only [Lp.toLp_coeFn] using p.2

end Torsion

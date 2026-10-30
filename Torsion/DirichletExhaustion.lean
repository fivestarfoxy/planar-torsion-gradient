import Torsion.DirichletGalerkin
import Torsion.SobolevExhaustion

/-!
# Strong H¹ convergence along increasing open-domain exhaustions

This is the variational convergence step in Lemma 3.7. It concerns the actual
weak torsion solutions and their original simultaneous Sobolev approximations.
Galerkin orthogonality proves a best-approximation bound for the weak gradients;
eventual admission of compact tests then yields strong L² gradient convergence.
The common bounded-domain Poincaré inequality gives strong L² value convergence.
No marked-boundary derivative convergence is asserted here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- The actual weak torsion gradients converge strongly in L² along an
increasing open-domain exhaustion. Existence is supplied by the proved weak
solution records; no derivative or energy convergence is assumed. -/
theorem IsWeakTorsion.tendsto_eLpNorm_gradient_of_exhaustion
    {D : ℕ → Set Plane} (hmono : Monotone D) (hopen : ∀ n, IsOpen (D n))
    {u : Plane → ℝ} {g : Plane → Plane}
    {uₙ : ℕ → Plane → ℝ} {gₙ : ℕ → Plane → Plane}
    (hu : IsWeakTorsion (⋃ n, D n) u g)
    (hun : ∀ n, IsWeakTorsion (D n) (uₙ n) (gₙ n)) :
    Tendsto (fun n => eLpNorm (fun x => gₙ n x - g x) 2 volume) atTop (𝓝 0) := by
  obtain ⟨_, _, f, hf, _, hfg⟩ := hu.1
  let G : ℕ → Lp Plane 2 (volume : Measure Plane) :=
    fun n => (hun n).1.2.1.toLp (gₙ n)
  let G₀ : Lp Plane 2 (volume : Measure Plane) := hu.1.2.1.toLp g
  let F : ℕ → Lp Plane 2 (volume : Measure Plane) :=
    fun k => (hf k).memLp_gradient.toLp (gradient (f k))
  have hF : Tendsto F atTop (𝓝 G₀) := by
    apply tendsto_iff_edist_tendsto_0.mpr
    simpa only [F, G₀, Lp.edist_toLp_toLp] using hfg
  have hG : Tendsto G atTop (𝓝 G₀) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp hF ε hε
    obtain ⟨N, hN⟩ := (hf k).exists_forall_ge_mem_exhaustion hopen hmono
    refine ⟨N, ?_⟩
    intro n hn
    have hcea := (hun n).cea_gradient_norm hu (hopen n).measurableSet
      (isOpen_iUnion hopen).measurableSet (subset_iUnion D n) (hN n hn)
    calc
      dist (G n) G₀ = ‖G n - G₀‖ := dist_eq_norm _ _
      _ ≤ ‖F k - G₀‖ := hcea
      _ = dist (F k) G₀ := (dist_eq_norm _ _).symm
      _ < ε := hk k le_rfl
  have hdist := tendsto_iff_edist_tendsto_0.mp hG
  simpa only [G, G₀, Lp.edist_toLp_toLp] using hdist

/-- On a common bounded union, both coordinates converge strongly in L².
This proves the full simultaneous H¹ convergence needed before the harmonic
regularity step of Lemma 3.7. -/
theorem IsWeakTorsion.tendsto_eLpNorm_of_exhaustion
    {D : ℕ → Set Plane} (hmono : Monotone D) (hopen : ∀ n, IsOpen (D n))
    (hbounded : Bornology.IsBounded (⋃ n, D n))
    {u : Plane → ℝ} {g : Plane → Plane}
    {uₙ : ℕ → Plane → ℝ} {gₙ : ℕ → Plane → Plane}
    (hu : IsWeakTorsion (⋃ n, D n) u g)
    (hun : ∀ n, IsWeakTorsion (D n) (uₙ n) (gₙ n)) :
    Tendsto (fun n => eLpNorm (fun x => uₙ n x - u x) 2 volume) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun x => gₙ n x - g x) 2 volume) atTop (𝓝 0) := by
  have hgrad := hu.tendsto_eLpNorm_gradient_of_exhaustion hmono hopen hun
  refine ⟨?_, hgrad⟩
  obtain ⟨K, _, hP⟩ := exists_poincare_constant_of_bounded hbounded
  have hbound (n : ℕ) : eLpNorm (fun x => uₙ n x - u x) 2 volume ≤
      ENNReal.ofReal K * eLpNorm (fun x => gₙ n x - g x) 2 volume :=
    hP _ _ (((hun n).1.mono (subset_iUnion D n)).sub hu.1)
  have hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) hgrad
    (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le _) hbound

end Torsion

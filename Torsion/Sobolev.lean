module

public import Torsion.SobolevAdd
public import Torsion.SobolevScalar
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Concrete Sobolev closure and uniqueness of the weak torsion gradient

Closure is established with the simultaneous smooth approximations in
`MemH10`. The difference of two weak solutions is consequently an admissible
test in their actual weak equations. Its Dirichlet energy vanishes, proving
that the weak gradients agree almost everywhere on the domain. No abstract
comparison certificate, PDE uniqueness axiom, or boundary regularity is used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Subtraction preserves the compactly supported smooth test core. -/
theorem IsTest.sub {D : Set Plane} {f g : Plane → ℝ}
    (hf : IsTest D f) (hg : IsTest D g) : IsTest D (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The actual Sobolev graph is closed under subtraction. -/
theorem MemH10.sub {D : Set Plane} {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : MemH10 D u g) (hv : MemH10 D v h) :
    MemH10 D (fun x => u x - v x) (fun x => g x - h x) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

/-- The graph predicate depends only on almost-everywhere value and gradient
classes; the same smooth approximation witnesses serve new representatives. -/
theorem MemH10.congr {D : Set Plane} {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : MemH10 D u g) (huv : u =ᵐ[volume] v) (hgh : g =ᵐ[volume] h) :
    MemH10 D v h := by
  rcases hu with ⟨hu, hg, f, hf, hfu, hfg⟩
  refine ⟨(memLp_congr_ae huv).mp hu, (memLp_congr_ae hgh).mp hg,
    f, hf, ?_, ?_⟩
  · have heq (n : ℕ) : eLpNorm (fun x => f n x - v x) 2 volume =
        eLpNorm (fun x => f n x - u x) 2 volume :=
      eLpNorm_congr_ae (EventuallyEq.rfl.sub huv.symm)
    simpa only [heq] using hfu
  · have heq (n : ℕ) : eLpNorm (fun x => gradient (f n) x - h x) 2 volume =
        eLpNorm (fun x => gradient (f n) x - g x) 2 volume :=
      eLpNorm_congr_ae (EventuallyEq.rfl.sub hgh.symm)
    simpa only [heq] using hfg

/-- The real inner product of two L² functions is integrable, by Hölder and
Cauchy–Schwarz. This is applied below on the restricted domain measure. -/
theorem integrable_real_inner_of_memLp_two
    {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : X → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner (𝕜 := ℝ) (f x) (g x)) μ := by
  apply (hf.norm.integrable_mul hg.norm).mono'
  · exact hf.aestronglyMeasurable.inner hg.aestronglyMeasurable
  · exact Eventually.of_forall (fun x => norm_inner_le_norm (f x) (g x))

/-- Weak torsion solutions have identical weak gradients almost everywhere
on the domain. The difference of their actual Sobolev data is the test. -/
theorem IsWeakTorsion.gradient_ae_eq {D : Set Plane}
    {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hv : IsWeakTorsion D v h) :
    g =ᵐ[volume.restrict D] h := by
  have htest := hu.1.sub hv.1
  have hequ := hu.2 (fun x => u x - v x) (fun x => g x - h x) htest
  have heqv := hv.2 (fun x => u x - v x) (fun x => g x - h x) htest
  have hgm : MemLp g 2 (volume.restrict D) := hu.1.2.1.restrict D
  have hhm : MemLp h 2 (volume.restrict D) := hv.1.2.1.restrict D
  have hdm : MemLp (fun x => g x - h x) 2 (volume.restrict D) := hgm.sub hhm
  have hgi := integrable_real_inner_of_memLp_two hgm hdm
  have hhi := integrable_real_inner_of_memLp_two hhm hdm
  have henergy : (∫ x in D, inner (𝕜 := ℝ) (g x - h x) (g x - h x)) = 0 := by
    calc
      (∫ x in D, inner (𝕜 := ℝ) (g x - h x) (g x - h x)) =
          ∫ x in D, (inner (𝕜 := ℝ) (g x) (g x - h x) -
            inner (𝕜 := ℝ) (h x) (g x - h x)) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => inner_sub_left _ _ _)
      _ = (∫ x in D, inner (𝕜 := ℝ) (g x) (g x - h x)) -
          ∫ x in D, inner (𝕜 := ℝ) (h x) (g x - h x) := integral_sub hgi hhi
      _ = 0 := by rw [hequ, heqv, sub_self]
  have hnormenergy : (∫ x in D, ‖g x - h x‖ ^ 2) = 0 := by
    simpa only [real_inner_self_eq_norm_sq] using henergy
  have hnormint : Integrable (fun x => ‖g x - h x‖ ^ 2) (volume.restrict D) :=
    (memLp_two_iff_integrable_sq_norm hdm.aestronglyMeasurable).mp hdm
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => sq_nonneg ‖g x - h x‖) hnormint).mp hnormenergy
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hx))

/-- In particular the gradient data of any two constructed Dirichlet solutions
are independent of the chosen solution record. -/
theorem DirichletSolution.weakGradient_ae_eq {D : Set Plane}
    (s t : DirichletSolution D) :
    s.weakGradient =ᵐ[volume.restrict D] t.weakGradient :=
  s.weakEquation.gradient_ae_eq t.weakEquation

/-- The essential torsion-gradient norm is independent of the choice of weak
solution supplied by a `DirichletTheory`. -/
theorem DirichletTheory.G_eq (S T : DirichletTheory) (D : ConvexDomain) :
    S.G D = T.G D := by
  exact eLpNorm_congr_ae ((S.solution D).weakGradient_ae_eq (T.solution D))

/-- Consequently the area-one supremum is independent of those choices too. -/
theorem DirichletTheory.cStar_eq (S T : DirichletTheory) : S.cStar = T.cStar := by
  unfold DirichletTheory.cStar
  congr 1
  funext D
  congr 1
  funext harea
  exact S.G_eq T D

end Torsion

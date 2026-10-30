import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Convex.Basic

/-!
# Concrete objects occurring in the planar torsion problem

These are definitions, not existence or regularity theorems. In particular,
`DirichletTheory` is a *parameter* of the later conditional theorem. The module
`HilbertDirichlet` constructs it from the actual closed Sobolev graph, proved
Poincaré inequality, and Lax--Milgram theorem.

A zero-extended H¹₀ function is represented by its value and weak gradient,
with simultaneous L² approximation by smooth functions compactly supported
inside the domain. This retains the distinction between H¹₀ and simply
vanishing almost everywhere outside a domain with slits (Lemma 3.2).
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

abbrev Plane := ℂ

/-- Smooth compactly supported test functions with support inside `D`. -/
def IsTest (D : Set Plane) (f : Plane → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ D

/-- The graph closure of C∞_c(D) for the zero-extended H¹ norm.
The supplied vector field `g` is the weak gradient, not a pointwise derivative
of an arbitrary representative of `u`. -/
def MemH10 (D : Set Plane) (u : Plane → ℝ) (g : Plane → Plane) : Prop :=
  MemLp u 2 volume ∧ MemLp g 2 volume ∧
  ∃ f : ℕ → Plane → ℝ,
    (∀ n, IsTest D (f n)) ∧
    Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 volume) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun x => gradient (f n) x - g x) 2 volume)
      atTop (𝓝 0)

/-- Equation (1.1), with all functions zero extended to the plane. -/
def IsWeakTorsion (D : Set Plane) (u : Plane → ℝ) (g : Plane → Plane) : Prop :=
  MemH10 D u g ∧
  ∀ (v : Plane → ℝ) (h : Plane → Plane), MemH10 D v h →
    (∫ x in D, inner (𝕜 := ℝ) (g x) (h x)) = ∫ x in D, v x

/-- The nonempty class used for the convex-domain theorem. The empty-domain
case can be added separately; it never occurs in the area-one supremum. -/
structure ConvexDomain where
  carrier : Set Plane
  isOpen : IsOpen carrier
  bounded : Bornology.IsBounded carrier
  convex : Convex ℝ carrier
  nonempty : carrier.Nonempty

namespace ConvexDomain

/-- Euclidean area. Boundedness makes the measure finite. -/
def area (D : ConvexDomain) : ℝ := (volume D.carrier).toReal

end ConvexDomain

/-- Weak solution data; existence/uniqueness is not postulated globally. -/
structure DirichletSolution (D : Set Plane) where
  value : Plane → ℝ
  weakGradient : Plane → Plane
  weakEquation : IsWeakTorsion D value weakGradient

/-- An explicit hypothesis supplying the weak solutions of Section 1. -/
structure DirichletTheory where
  solution : ∀ D : ConvexDomain, DirichletSolution D.carrier

namespace DirichletTheory

/-- G(D), using an essential supremum over the interior, not a boundary norm.
The ENNReal codomain retains the possibility of an infinite gradient norm. -/
def G (T : DirichletTheory) (D : ConvexDomain) : ℝ≥0∞ :=
  eLpNorm (T.solution D).weakGradient ∞ (volume.restrict D.carrier)

/-- The area-one supremum in Section 1. -/
def cStar (T : DirichletTheory) : ℝ≥0∞ :=
  ⨆ D : ConvexDomain, ⨆ (_ : D.area = 1), T.G D

end DirichletTheory

/-- The positive half-plane used for marked domains. -/
def upperHalfPlane : Set Plane := {z | 0 < z.im}

/-- Definition 3.1, including the common flat neighborhood. -/
def IsMarked (D : Set Plane) : Prop :=
  IsOpen D ∧ Bornology.IsBounded D ∧ D ⊆ upperHalfPlane ∧
  ∃ r : ℝ, 0 < r ∧ D ∩ Metric.ball 0 r = upperHalfPlane ∩ Metric.ball 0 r

/-- Equation (3.4). Endpoint values do not appear in the open domain. -/
def radialDomain (R : ℝ → ℝ) : Set Plane :=
  {z | ∃ θ r : ℝ, 0 < θ ∧ θ < Real.pi ∧ 0 < r ∧ r < R θ ∧
    z = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)}

/-- The profile-side area expression (3.5); its identification with geometric
area is a polar-coordinate theorem, not built into the definition. -/
def radialArea (R : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ θ in Ioo 0 Real.pi, (R θ) ^ 2

/-- Marked inward derivative, when regularity supplies the indicated limit.
This is a relation, so no derivative is silently assigned to irregular data. -/
def HasMarkedFlux (u : Plane → ℝ) (q : ℝ) : Prop :=
  Tendsto (fun t : ℝ => u ((t : ℂ) * Complex.I) / t) (𝓝[>] 0) (𝓝 q)

end Torsion

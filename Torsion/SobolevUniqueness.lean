module

public import Torsion.Sobolev
public import Torsion.SobolevSupport
public import Torsion.Poincare

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Uniqueness of the concrete weak Dirichlet torsion problem

The zero-extension result upgrades equality of weak gradients on the domain to
whole-plane equality. The proved Poincaré inequality then also gives equality
of the solution values. These are consequences of the actual graph-closure and
variational definitions, without a uniqueness assumption.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Zero extension upgrades domain-wise weak-gradient uniqueness to global
almost-everywhere uniqueness on any measurable domain. -/
theorem IsWeakTorsion.gradient_global_ae_eq {D : Set Plane} (hD : MeasurableSet D)
    {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hv : IsWeakTorsion D v h) : g =ᵐ[volume] h := by
  have hinside := (ae_restrict_iff' hD).mp (hu.gradient_ae_eq hv)
  have hgoff := (ae_restrict_iff' hD.compl).mp hu.1.gradient_ae_zero_off
  have hhoff := (ae_restrict_iff' hD.compl).mp hv.1.gradient_ae_zero_off
  filter_upwards [hinside, hgoff, hhoff] with x hi hg hh
  by_cases hx : x ∈ D
  · exact hi hx
  · exact (hg hx).trans (hh hx).symm

/-- The weak torsion value is unique almost everywhere on a bounded convex
domain, by testing the difference and applying the proved Poincaré estimate. -/
theorem IsWeakTorsion.value_ae_eq {D : ConvexDomain}
    {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : IsWeakTorsion D.carrier u g) (hv : IsWeakTorsion D.carrier v h) :
    u =ᵐ[volume] v := by
  have hgrad := hu.gradient_global_ae_eq D.isOpen.measurableSet hv
  have htest := hu.1.sub hv.1
  have hdiffgrad : (fun x => g x - h x) =ᵐ[volume] 0 := by
    filter_upwards [hgrad] with x hx
    simp only [hx, sub_self, Pi.zero_apply]
  have hgradnorm : eLpNorm (fun x => g x - h x) 2 volume = 0 :=
    (eLpNorm_eq_zero_iff (by norm_num)).mpr hdiffgrad
  have hvaluenorm : eLpNorm (fun x => u x - v x) 2 volume = 0 := by
    apply le_antisymm
    · simpa only [hgradnorm, mul_zero] using htest.poincare
    · exact zero_le
  have hdiffvalue := (eLpNorm_eq_zero_iff (by norm_num)).mp hvaluenorm
  filter_upwards [hdiffvalue] with x hx
  exact sub_eq_zero.mp hx

/-- Both coordinates of any two concrete Dirichlet solution records agree
almost everywhere. -/
theorem DirichletSolution.ae_unique {D : ConvexDomain}
    (s t : DirichletSolution D.carrier) :
    s.value =ᵐ[volume] t.value ∧ s.weakGradient =ᵐ[volume] t.weakGradient :=
  ⟨s.weakEquation.value_ae_eq t.weakEquation,
    s.weakEquation.gradient_global_ae_eq D.isOpen.measurableSet t.weakEquation⟩

end Torsion

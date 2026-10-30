module

public import Torsion.Sobolev
public import Torsion.SobolevSupport
public import Torsion.BoundedDomains
public import Mathlib.Tactic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual global weak equation and Galerkin orthogonality

The zero-extension theorem converts the domain integrals in the concrete weak
equation to full-plane L² inner products. Nested-domain solutions are therefore
orthogonal to every Sobolev test on the smaller domain, yielding the best
approximation estimate used for increasing-domain convergence.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- The domain weak equation is the global L²-gradient equation, using the
proved almost-everywhere zero extensions of the actual Sobolev data. -/
theorem IsWeakTorsion.global_weak_equation {D : Set Plane}
    {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : MeasurableSet D) (hv : MemH10 D v h) :
    inner (𝕜 := ℝ) (hu.1.2.1.toLp g) (hv.2.1.toLp h) = ∫ x, v x := by
  have hgzero : ∀ᵐ x ∂volume, x ∉ D → g x = 0 :=
    (ae_restrict_iff' hD.compl).mp hu.1.gradient_ae_zero_off
  have hvzero : ∀ᵐ x ∂volume, x ∉ D → v x = 0 :=
    (ae_restrict_iff' hD.compl).mp hv.value_ae_zero_off
  calc
    _ = ∫ x, inner (𝕜 := ℝ) (g x) (h x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hu.1.2.1.coeFn_toLp, hv.2.1.coeFn_toLp] with x hg hh
      rw [hg, hh]
    _ = ∫ x in D, inner (𝕜 := ℝ) (g x) (h x) := by
      symm
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [hgzero] with x hx hnx
      simp only [hx hnx, inner_zero_left]
    _ = ∫ x in D, v x := hu.2 v h hv
    _ = ∫ x, v x := setIntegral_eq_integral_of_ae_compl_eq_zero hvzero

/-- The difference of nested-domain weak torsion gradients is orthogonal to
every genuine Sobolev test on the smaller domain. -/
theorem IsWeakTorsion.galerkin_orthogonality {D E : Set Plane}
    {u v w : Plane → ℝ} {g h k : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hv : IsWeakTorsion E v h)
    (hD : MeasurableSet D) (hE : MeasurableSet E) (hDE : D ⊆ E)
    (hw : MemH10 D w k) :
    inner (𝕜 := ℝ) (hu.1.2.1.toLp g - hv.1.2.1.toLp h) (hw.2.1.toLp k) = 0 := by
  rw [inner_sub_left, hu.global_weak_equation hD hw,
    hv.global_weak_equation hE (hw.mono hDE), sub_self]

/-- The nested-domain gradient error is at most the error of any actual
zero-boundary Sobolev approximation on the smaller domain. -/
theorem IsWeakTorsion.cea_gradient_norm_of_memH10 {D E : Set Plane}
    {u v w : Plane → ℝ} {g h k : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hv : IsWeakTorsion E v h)
    (hD : MeasurableSet D) (hE : MeasurableSet E) (hDE : D ⊆ E)
    (hw : MemH10 D w k) :
    ‖hu.1.2.1.toLp g - hv.1.2.1.toLp h‖ ≤
      ‖hw.2.1.toLp k - hv.1.2.1.toLp h‖ := by
  have hortho := hu.galerkin_orthogonality hv hD hE hDE (hu.1.sub hw)
  have hsub : (hu.1.sub hw).2.1.toLp (fun x => g x - k x) =
      hu.1.2.1.toLp g - hw.2.1.toLp k :=
    hu.1.2.1.toLp_sub hw.2.1
  rw [hsub] at hortho
  have hpyth := norm_sub_sq_eq_norm_sq_add_norm_sq_real hortho
  have hid : (hu.1.2.1.toLp g - hv.1.2.1.toLp h) -
        (hu.1.2.1.toLp g - hw.2.1.toLp k) =
      hw.2.1.toLp k - hv.1.2.1.toLp h := by abel
  rw [hid] at hpyth
  nlinarith [norm_nonneg (hu.1.2.1.toLp g - hv.1.2.1.toLp h),
    norm_nonneg (hw.2.1.toLp k - hv.1.2.1.toLp h),
    sq_nonneg ‖hu.1.2.1.toLp g - hw.2.1.toLp k‖]

/-- In particular every smooth compact test in the smaller domain provides a
best-approximation bound for its true weak torsion gradient. -/
theorem IsWeakTorsion.cea_gradient_norm {D E : Set Plane}
    {u v f : Plane → ℝ} {g h : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hv : IsWeakTorsion E v h)
    (hD : MeasurableSet D) (hE : MeasurableSet E) (hDE : D ⊆ E)
    (hf : IsTest D f) :
    ‖hu.1.2.1.toLp g - hv.1.2.1.toLp h‖ ≤
      ‖hf.memLp_gradient.toLp (gradient f) - hv.1.2.1.toLp h‖ :=
  hu.cea_gradient_norm_of_memH10 hv hD hE hDE hf.memH10

end Torsion

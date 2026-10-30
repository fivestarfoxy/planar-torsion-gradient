module

public import Torsion.MarkedTorsionTaylor
public import Torsion.CanonicalSupportingFlux
public import Torsion.WeakTorsionRepresentative
public import Torsion.SupportedConvexFlatHull

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual pointwise comparison with the calibrated marked outer domain

Weak comparison is transferred to actual continuous interior representatives.
The uniformly controlled normal quotient of the outer torsion representative
then gives the sharp spectral boundary-collar estimate for the original
solution at every common normal-ray point.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Domain monotonicity holds pointwise for the actual continuous interior
representatives, despite the weak PDE initially providing only a.e. order. -/
theorem IsWeakTorsion.le_on_continuous_representatives
    {D E : Set Plane} {u v U W : Plane → ℝ} {g k : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hv : IsWeakTorsion E v k)
    (hD : IsOpen D) (hE : IsOpen E)
    (hbD : Bornology.IsBounded D) (hbE : Bornology.IsBounded E) (hDE : D ⊆ E)
    (hU : ContinuousOn U D) (hW : ContinuousOn W E)
    (hUrep : u =ᵐ[volume.restrict D] U) (hWrep : v =ᵐ[volume.restrict E] W) :
    ∀ x ∈ D, U x ≤ W x := by
  have hmono := hu.mono hv hD hE hbD hbE hDE
  have heq : (fun z => max (U z) (W z)) =ᵐ[volume.restrict D] W := by
    filter_upwards [ae_restrict_of_ae hmono, hUrep,
      ae_restrict_of_ae_restrict_of_subset hDE hWrep] with z hz hzu hzv
    exact max_eq_right (by simpa only [← hzu, ← hzv] using hz)
  have hpoint := Measure.eqOn_open_of_ae_eq heq hD (hU.sup (hW.mono hDE)) (hW.mono hDE)
  intro x hx
  exact max_eq_right_iff.mp (hpoint hx)

/-- Adding a horizontal base and taking its actual convex outer hull does
not increase the domain's upper height. This is uniform in the base radius. -/
theorem flatOuterHull_subset_upper_height {D : Set Plane} {b : ℝ}
    (hb : 0 ≤ b) (hheight : ∀ z ∈ D, z.im ≤ b) (s : ℝ) :
    ∀ z ∈ flatOuterHull D s, z.im < b := by
  have hcl : closure D ⊆ {z : Plane | z.im ≤ b} :=
    (isClosed_le Complex.continuous_im continuous_const).closure_subset_iff.mpr hheight
  have hbase : horizontalBase s ⊆ {z : Plane | z.im ≤ b} := by
    intro z hz
    change z.im ≤ b
    rw [hz.2]
    exact hb
  have hh := convexHull_min (union_subset hcl hbase) (convex_halfSpace_im_le b)
  have hi := interior_mono hh
  simpa only [flatOuterHull, Complex.interior_setOf_im_le] using hi

/-- The actual continuous original torsion representative at a common
normal-ray point is bounded by the sharp spectral area term and a uniform
quadratic remainder from the actual marked outer weak torsion problem. -/
theorem exists_uniform_second_spectral_collar_comparison_constant {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {D E : ConvexDomain} {u U : Plane → ℝ}
      {g : Plane → Plane} {b : ℝ},
      IsWeakTorsion D.carrier u g → ContinuousOn U D.carrier →
      (u =ᵐ[volume.restrict D.carrier] U) → D.carrier ⊆ E.carrier →
      IsMarked E.carrier → 0 ≤ b →
      upperHalfPlane ∩ Metric.ball (0 : Plane) (4*r) ⊆ E.carrier →
      (∀ z ∈ E.carrier, z.im < b) →
      ∀ h : ℝ, 0 < h → h < r/2 → (h : Plane)*Complex.I ∈ D.carrier →
        U ((h : Plane)*Complex.I) ≤
          (Spectral.spectralConstant Spectral.secondEigenvalue Spectral.secondEigenfunction *
            Real.sqrt E.area + (C*(2*r*b+8*r^2)+1/2)*h)*h := by
  obtain ⟨C, hC, hTaylor⟩ :=
    exists_uniform_slab_marked_torsion_normal_quotient_constant_on_representative hr
  refine ⟨C, hC, ?_⟩
  intro D E u U g b hu hU hUrep hDE hE hb hhalf hheight h hh hhR hhD
  obtain ⟨v⟩ := HilbertDirichlet.exists_dirichletSolution_of_bounded E.isOpen.measurableSet E.bounded
  have hv := v.weakEquation
  obtain ⟨W, hW, hWzero, hWrep, hWG⟩ := hv.exists_smooth_representative E.isOpen E.bounded
  have hcompare := hu.le_on_continuous_representatives hv D.isOpen E.isOpen
    D.bounded E.bounded hDE hU hW.continuousOn hUrep hWrep
  have herror := hTaylor hE hv hb hhalf hheight hW.continuousOn hWrep h hh hhR
  have hline : Tendsto (fun t : ℝ => (t : Plane)*Complex.I) (𝓝[>] 0) (𝓝 (0 : Plane)) := by
    simpa using (((Complex.continuous_ofReal.tendsto 0).mul_const Complex.I).mono_left
      nhdsWithin_le_nhds)
  have hzero : (0 : Plane) ∈ closure E.carrier :=
    mem_closure_of_tendsto hline ((eventually_vertical_mem_halfBall (r := 4*r) (by positivity)).mono
      (fun _ ht => hhalf ht))
  have hflux := (torsionFlux_spec hE).le_second_spectral_bound hzero hE.2.2.1
  apply (hcompare _ hhD).trans
  apply (div_le_iff₀ hh).mp
  have herr := (le_abs_self (W ((h : Plane)*Complex.I)/h-torsionFlux E.carrier)).trans herror
  linarith

end Torsion

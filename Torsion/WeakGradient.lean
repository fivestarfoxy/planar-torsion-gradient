module

public import Torsion.SobolevGraph
public import Torsion.BoundedDomains
public import Torsion.Sobolev
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Identification of the actual distributional weak gradient

Integration by parts is proved for the smooth core. Its defect is a
continuous linear functional on the actual value/gradient L² product;
the kernel is closed, so it contains the entire H¹₀ graph closure.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace Torsion

/-- The defining integration-by-parts identity for the distributional gradient. -/
def HasDistributionalGradient (u : Plane → ℝ) (g : Plane → Plane) : Prop :=
  ∀ (ψ : Plane → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ v : Plane,
    (∫ x, u x * fderiv ℝ ψ x v) = - ∫ x, inner (𝕜 := ℝ) (g x) v * ψ x

/-- The classical gradient represents the real Fréchet derivative, including
at nondifferentiable points where both are defined using `fderiv`. -/
theorem fderiv_apply_eq_inner_gradient (f : Plane → ℝ) (x v : Plane) :
    fderiv ℝ f x v = inner (𝕜 := ℝ) (gradient f x) v := by
  exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := v)
    (y := fderiv ℝ f x)).symm

namespace WeakGradient

private theorem memLp_directional {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) (v : Plane) : MemLp (fun x => fderiv ℝ ψ x v) 2 volume := by
  apply ((innerSL ℝ v).comp_memLp' (hψ.memLp_gradient (p := 2))).ae_eq
  apply ae_of_all
  intro x
  simp only [Function.comp_apply, innerSL_apply_apply, fderiv_apply_eq_inner_gradient,
    real_inner_comm]

private theorem memLp_testVector {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) (v : Plane) : MemLp (fun x => ψ x • v) 2 volume :=
  (ContinuousLinearMap.toSpanSingleton ℝ v).comp_memLp' (hψ.memLp_value (p := 2))

private def defect {ψ : Plane → ℝ} (hψ : IsTest univ ψ) (v : Plane) :
    SobolevPair →L[ℝ] ℝ :=
  (innerSL ℝ ((memLp_directional hψ v).toLp (fun x => fderiv ℝ ψ x v))).comp
      (ContinuousLinearMap.fst ℝ _ _) +
    (innerSL ℝ ((memLp_testVector hψ v).toLp (fun x => ψ x • v))).comp
      (ContinuousLinearMap.snd ℝ _ _)

private theorem defect_apply {ψ : Plane → ℝ} (hψ : IsTest univ ψ) (v : Plane)
    (p : SobolevPair) : defect hψ v p =
      (∫ x, p.1 x * fderiv ℝ ψ x v) + ∫ x, inner (𝕜 := ℝ) (p.2 x) v * ψ x := by
  change inner (𝕜 := ℝ) ((memLp_directional hψ v).toLp _) p.1 +
    inner (𝕜 := ℝ) ((memLp_testVector hψ v).toLp _) p.2 = _
  rw [L2.inner_def, L2.inner_def]
  congr 1
  · apply integral_congr_ae
    filter_upwards [(memLp_directional hψ v).coeFn_toLp] with x hx
    rw [hx]
    simp [mul_comm]
  · apply integral_congr_ae
    filter_upwards [(memLp_testVector hψ v).coeFn_toLp] with x hx
    rw [hx, real_inner_smul_left, real_inner_comm]
    ring

private theorem defect_toLp {ψ u : Plane → ℝ} {g : Plane → Plane}
    (hψ : IsTest univ ψ) (v : Plane) (hu : MemLp u 2 volume) (hg : MemLp g 2 volume) :
    defect hψ v (hu.toLp u, hg.toLp g) =
      (∫ x, u x * fderiv ℝ ψ x v) + ∫ x, inner (𝕜 := ℝ) (g x) v * ψ x := by
  rw [defect_apply]
  congr 1
  · apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]

private theorem smooth_integration_by_parts {D : Set Plane} {f ψ : Plane → ℝ}
    (hf : IsTest D f) (hψ : IsTest univ ψ) (v : Plane) :
    (∫ x, f x * fderiv ℝ ψ x v) = - ∫ x, inner (𝕜 := ℝ) (gradient f x) v * ψ x := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((memLp_directional hf v).integrable_mul (hψ.memLp_value (p := 2)))
    ((hf.memLp_value (p := 2)).integrable_mul (memLp_directional hψ v))
    ((hf.memLp_value (p := 2)).integrable_mul (hψ.memLp_value (p := 2)))
    (fun x _ => hf.1.differentiable (by simp) x)
    (fun x _ => hψ.1.differentiable (by simp) x)
  simpa only [fderiv_apply_eq_inner_gradient] using h

/-- The continuous defect vanishes on the entire concrete graph closure. -/
private theorem graph_in_defect_kernel {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest univ ψ) (v : Plane) :
    H10Graph D ≤ LinearMap.ker (defect hψ v).toLinearMap := by
  apply (testGraphSubmodule D).topologicalClosure_minimal
  · rintro p ⟨f, hf, rfl⟩
    change defect hψ v hf.graph = 0
    rw [IsTest.graph, defect_toLp]
    have h := smooth_integration_by_parts hf hψ v
    linarith
  · exact ContinuousLinearMap.isClosed_ker (defect hψ v)

end WeakGradient

/-- A pair in the originally defined H¹₀ graph has the actual distributional
gradient, with no additional regularity or boundary assumptions. -/
theorem MemH10.distributionalGradient {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) : HasDistributionalGradient u g := by
  intro ψ hdiff hcompact v
  let hψ : IsTest univ ψ := ⟨hdiff, hcompact, subset_univ _⟩
  have hmem := WeakGradient.graph_in_defect_kernel hψ v
    ((memH10_iff_mem_H10Graph hu.1 hu.2.1).mp hu)
  change WeakGradient.defect hψ v (hu.1.toLp u, hu.2.1.toLp g) = 0 at hmem
  rw [WeakGradient.defect_toLp] at hmem
  linarith

namespace WeakGradient

private theorem memLp_component {g : Plane → Plane} (hg : MemLp g 2 volume) (v : Plane) :
    MemLp (fun x => inner (𝕜 := ℝ) (g x) v) 2 volume := by
  apply ((innerSL ℝ v).comp_memLp' hg).ae_eq
  exact ae_of_all _ fun x => (real_inner_comm v (g x)).symm

/-- Equality of distributional gradients in each direction, with actual
locally integrable scalar components. -/
theorem component_ae_eq {u w : Plane → ℝ} {g h : Plane → Plane}
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hgu : HasDistributionalGradient u g) (hhw : HasDistributionalGradient w h)
    (huw : u =ᵐ[volume] w) (v : Plane) :
    (fun x => inner (𝕜 := ℝ) (g x) v) =ᵐ[volume] (fun x => inner (𝕜 := ℝ) (h x) v) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((memLp_component hg v).locallyIntegrable (by norm_num))
    ((memLp_component hh v).locallyIntegrable (by norm_num))
  intro ψ hdiff hcompact
  have heq : (∫ x, u x * fderiv ℝ ψ x v) = ∫ x, w x * fderiv ℝ ψ x v :=
    integral_congr_ae (huw.mul EventuallyEq.rfl)
  have h1 := hgu ψ hdiff hcompact v
  have h2 := hhw ψ hdiff hcompact v
  have hright : (∫ x, inner (𝕜 := ℝ) (g x) v * ψ x) =
      ∫ x, inner (𝕜 := ℝ) (h x) v * ψ x := by linarith
  simpa only [smul_eq_mul, mul_comm] using hright

end WeakGradient

/-- A real distributional gradient is uniquely determined by the a.e. class
of its value function. The two planar coordinate directions suffice. -/
theorem HasDistributionalGradient.unique_ae {u w : Plane → ℝ} {g h : Plane → Plane}
    (hgu : HasDistributionalGradient u g) (hhw : HasDistributionalGradient w h)
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) (huw : u =ᵐ[volume] w) :
    g =ᵐ[volume] h := by
  have h1 := WeakGradient.component_ae_eq hg hh hgu hhw huw (1 : Plane)
  have hI := WeakGradient.component_ae_eq hg hh hgu hhw huw Complex.I
  filter_upwards [h1, hI] with x hx1 hxI
  apply Complex.ext
  · simpa [Complex.inner] using hx1
  · simpa [Complex.inner, Complex.mul_re] using hxI

/-- Uniqueness of the actual weak gradient in the H¹₀ graph. The two domains
may differ; the zero-extended value's a.e. class determines its gradient. -/
theorem MemH10.gradient_ae_eq_of_value_ae_eq
    {D E : Set Plane} {u w : Plane → ℝ} {g h : Plane → Plane}
    (hu : MemH10 D u g) (hw : MemH10 E w h) (huw : u =ᵐ[volume] w) :
    g =ᵐ[volume] h :=
  hu.distributionalGradient.unique_ae hw.distributionalGradient hu.2.1 hw.2.1 huw

/-- Every weak torsion solution satisfies the classical-test weak Poisson
equation. This is the distributional PDE input to interior regularity. -/
theorem IsWeakTorsion.smooth_test_equation {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g)
    {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    (∫ x in D, inner (𝕜 := ℝ) (g x) (gradient ψ x)) = ∫ x in D, ψ x :=
  hu.2 ψ (gradient ψ) hψ.memH10

/-- The weak difference of two solutions of the same Poisson equation is
harmonic against every smooth compactly supported test. -/
theorem IsWeakTorsion.difference_weakly_harmonic {D : Set Plane}
    {u w : Plane → ℝ} {g h : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hw : IsWeakTorsion D w h)
    {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    (∫ x in D, inner (𝕜 := ℝ) (g x - h x) (gradient ψ x)) = 0 := by
  have hgint := integrable_real_inner_of_memLp_two (hu.1.2.1.restrict D)
    (hψ.memLp_gradient (p := 2) |>.restrict D)
  have hhint := integrable_real_inner_of_memLp_two (hw.1.2.1.restrict D)
    (hψ.memLp_gradient (p := 2) |>.restrict D)
  simp only [inner_sub_left]
  rw [integral_sub hgint hhint, hu.smooth_test_equation hψ,
    hw.smooth_test_equation hψ, sub_self]

/-- The global smooth-test Poisson equation. Compact test support makes the
restricted and zero-extended integrals exactly equal. -/
theorem IsWeakTorsion.global_smooth_test_equation {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g)
    {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    (∫ x, inner (𝕜 := ℝ) (g x) (gradient ψ x)) = ∫ x, ψ x := by
  have heq := hu.smooth_test_equation hψ
  have hleft : (∫ x in D, inner (𝕜 := ℝ) (g x) (gradient ψ x)) =
      ∫ x, inner (𝕜 := ℝ) (g x) (gradient ψ x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hnot : x ∉ tsupport ψ := fun h => hx (hψ.2.2 h)
    rw [gradient_eq_zero_of_not_mem_tsupport hnot, inner_zero_right]
  have hright : (∫ x in D, ψ x) = ∫ x, ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hψ.2.2 h))
  rwa [hleft, hright] at heq

/-- A concrete weak harmonic pair on an open region, stated using compact
smooth tests and the actual distributional gradient. -/
def IsWeakHarmonicOn (U : Set Plane) (u : Plane → ℝ) (g : Plane → Plane) : Prop :=
  HasDistributionalGradient u g ∧
    ∀ ψ : Plane → ℝ, IsTest U ψ → ∫ x, inner (𝕜 := ℝ) (g x) (gradient ψ x) = 0

/-- Torsion solutions on different domains have a genuinely weakly harmonic
difference on every common subdomain. This is the local equation used for
increasing-domain convergence and interior comparison. -/
theorem IsWeakTorsion.difference_weakHarmonicOn
    {D E U : Set Plane} {u w : Plane → ℝ} {g h : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hw : IsWeakTorsion E w h)
    (hUD : U ⊆ D) (hUE : U ⊆ E) :
    IsWeakHarmonicOn U (fun x => u x - w x) (fun x => g x - h x) := by
  refine ⟨((hu.1.mono subset_union_left).sub (hw.1.mono subset_union_right)).distributionalGradient, ?_⟩
  intro ψ hψ
  have hgint := integrable_real_inner_of_memLp_two hu.1.2.1 (hψ.memLp_gradient (p := 2))
  have hhint := integrable_real_inner_of_memLp_two hw.1.2.1 (hψ.memLp_gradient (p := 2))
  simp only [inner_sub_left]
  rw [integral_sub hgint hhint, hu.global_smooth_test_equation (hψ.mono hUD),
    hw.global_smooth_test_equation (hψ.mono hUE), sub_self]

end Torsion

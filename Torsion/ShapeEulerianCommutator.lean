module

public import Torsion.ShapeEnergyOperatorMatrix
public import Torsion.ClassicalWeakLaplacian
public import Torsion.WeakHarmonicWeyl.Classical
public import Torsion.ShapeForcing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The actual local Eulerian shape commutator

The differentiated physical energy coefficient is `(div V)I-DV-DV*`.
Compact-test integration by parts identifies its commutator with the actual
convective derivative `V · grad u`. This is an interior identity over the
original scalar functions and weak-test integrals. It does not assume a
shape derivative, a Hadamard formula or a boundary trace identity.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion.Shape

/-- The first variation of the physical gradient-energy coefficient,
acting on physical vectors rather than coordinate labels. -/
def energyVariationOperator (V : Plane → Plane) (x : Plane) : Plane →L[ℝ] Plane :=
  divergence V x • ContinuousLinearMap.id ℝ Plane - fderiv ℝ V x -
    (fderiv ℝ V x).adjoint

theorem realMatrix_energyVariationOperator (V : Plane → Plane) (x : Plane) :
    realMatrix (energyVariationOperator V x) = energyVariation (realMatrix (fderiv ℝ V x)) := by
  change LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
    (divergence V x • LinearMap.id - (fderiv ℝ V x).toLinearMap -
      ((fderiv ℝ V x).adjoint).toLinearMap) = _
  rw [map_sub, map_sub, map_smul, LinearMap.toMatrix_id]
  change divergence V x • 1 - realMatrix (fderiv ℝ V x) -
    realMatrix (fderiv ℝ V x).adjoint = _
  rw [realMatrix_adjoint]
  simp only [energyVariation, trace_realMatrix, divergence]

private theorem integral_compact_inner_gradient {F : Plane → Plane} (hF : Continuous F)
    {D : Set Plane} {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    Integrable (fun x => inner (𝕜 := ℝ) (F x) (gradient ψ x)) := by
  apply (hF.inner hψ.continuous_gradient).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact hψ.2.1
  intro x hx
  by_contra hn
  exact hx (by simp [gradient_eq_zero_of_not_mem_tsupport hn])

/-- A smooth field paired with the actual compact test gradient is again
a genuine compact smooth test, with support inside the original domain. -/
theorem IsTest_inner_gradient {D : Set Plane} {ψ : Plane → ℝ} (hψ : IsTest D ψ)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) :
    IsTest D (fun x => inner (𝕜 := ℝ) (V x) (gradient ψ x)) := by
  have hs : Function.support (fun x => inner (𝕜 := ℝ) (V x) (gradient ψ x)) ⊆ tsupport ψ := by
    intro x hx
    by_contra hn
    exact hx (by simp [gradient_eq_zero_of_not_mem_tsupport hn])
  exact ⟨hV.inner ℝ (WeakHarmonicRegularity.gradient_contDiff hψ.1),
    HasCompactSupport.of_support_subset_isCompact hψ.2.1 hs,
    (closure_minimal hs (isClosed_tsupport ψ)).trans hψ.2.2⟩

/-- Actual compact-test integration by parts for the divergence of an
arbitrary smooth physical vector field. No compactness of that field is
needed, because the scalar test and its derivative have compact support. -/
theorem divergence_smooth_test_pairing {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    {D : Set Plane} {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    (∫ x, divergence V x * ψ x) =
      -(∫ x, inner (𝕜 := ℝ) (V x) (gradient ψ x)) := by
  have hcoord (e : Plane) (C : Plane →L[ℝ] ℝ) :
      (∫ x, C (V x) * fderiv ℝ ψ x e) =
        -(∫ x, C (fderiv ℝ V x e) * ψ x) := by
    have hC : ContDiff ℝ ∞ (fun x => C (V x)) := C.contDiff.comp hV
    have hd (x : Plane) : fderiv ℝ (fun y => C (V y)) x e = C (fderiv ℝ V x e) := by
      change fderiv ℝ ((C : Plane → ℝ) ∘ V) x e = _
      rw [(C.hasFDerivAt.comp x ((hV.differentiable (by simp)) x).hasFDerivAt).fderiv]
      rfl
    have hdc : Continuous (fun x => C (fderiv ℝ V x e)) :=
      C.continuous.comp ((hV.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hψdc : Continuous (fun x => fderiv ℝ ψ x e) :=
      (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hi₁ : Integrable (fun x => fderiv ℝ (fun y => C (V y)) x e * ψ x) := by
      simp_rw [hd]
      exact (hdc.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
    have hi₂ : Integrable (fun x => C (V x) * fderiv ℝ ψ x e) :=
      (hC.continuous.mul hψdc).integrable_of_hasCompactSupport
        (hψ.2.1.fderiv_apply ℝ e).mul_left
    have hi₃ : Integrable (fun x => C (V x) * ψ x) :=
      (hC.continuous.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
    simpa only [hd] using integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      hi₁ hi₂ hi₃ (fun x _ => (hC.differentiable (by simp)) x)
      (fun x _ => (hψ.1.differentiable (by simp)) x)
  have h₁ := hcoord (1 : Plane) Complex.reCLM
  have h₂ := hcoord Complex.I Complex.imCLM
  change (∫ x, (V x).re * fderiv ℝ ψ x 1) =
    -(∫ x, (fderiv ℝ V x 1).re * ψ x) at h₁
  change (∫ x, (V x).im * fderiv ℝ ψ x Complex.I) =
    -(∫ x, (fderiv ℝ V x Complex.I).im * ψ x) at h₂
  have hi (e : Plane) (C : Plane →L[ℝ] ℝ) :
      Integrable (fun x => C (fderiv ℝ V x e) * ψ x) :=
    ((C.continuous.comp ((hV.continuous_fderiv (by simp)).clm_apply continuous_const)).mul
      hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
  have hj (e : Plane) (C : Plane →L[ℝ] ℝ) :
      Integrable (fun x => C (V x) * fderiv ℝ ψ x e) :=
    ((C.continuous.comp hV.continuous).mul
      ((hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
        (hψ.2.1.fderiv_apply ℝ e).mul_left
  have hp (x : Plane) : inner (𝕜 := ℝ) (V x) (gradient ψ x) =
      (V x).re * fderiv ℝ ψ x (1 : Plane) +
        (V x).im * fderiv ℝ ψ x Complex.I := by
    simp [fderiv_apply_eq_inner_gradient, Complex.inner, Complex.mul_re,
      -inner_gradient_left, -inner_gradient_right]
    ring
  have hi₁ : Integrable (fun x => ((fderiv ℝ V x) 1).re * ψ x) := hi 1 Complex.reCLM
  have hi₂ : Integrable (fun x => ((fderiv ℝ V x) Complex.I).im * ψ x) := hi Complex.I Complex.imCLM
  have hj₁ : Integrable (fun x => (V x).re * fderiv ℝ ψ x 1) := hj 1 Complex.reCLM
  have hj₂ : Integrable (fun x => (V x).im * fderiv ℝ ψ x Complex.I) := hj Complex.I Complex.imCLM
  simp_rw [divergence, add_mul, hp]
  rw [integral_add hi₁ hi₂, integral_add hj₁ hj₂]
  linarith

/-- The actual classical gradient of the convective derivative, using the
proved symmetry of the genuine Hessian. -/
theorem gradient_inner_gradient {V : Plane → Plane} {u : Plane → ℝ}
    (hV : ContDiff ℝ ∞ V) (hu : ContDiff ℝ ∞ u) (x : Plane) :
    gradient (fun y => inner (𝕜 := ℝ) (V y) (gradient u y)) x =
      (fderiv ℝ V x).adjoint (gradient u x) + fderiv ℝ (gradient u) x (V x) := by
  apply ext_inner_right ℝ
  intro e
  rw [← fderiv_apply_eq_inner_gradient,
    fderiv_inner_apply ℝ ((hV.differentiable (by simp)) x)
      (((WeakHarmonicRegularity.gradient_contDiff hu).differentiable (by simp)) x) e,
    inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    WeakHarmonicRegularity.fderiv_gradient_inner_symm hu]
  simp only [real_inner_comm]
  exact add_comm _ _

theorem eulerian_commutator_pointwise {V : Plane → Plane} {u ψ : Plane → ℝ}
    (hV : ContDiff ℝ ∞ V) (hu : ContDiff ℝ ∞ u) (hψ : ContDiff ℝ ∞ ψ) (x : Plane) :
    inner (𝕜 := ℝ) (gradient (fun y => inner (𝕜 := ℝ) (V y) (gradient u y)) x)
        (gradient ψ x) +
      inner (𝕜 := ℝ) (energyVariationOperator V x (gradient u x)) (gradient ψ x) =
      divergence V x * inner (𝕜 := ℝ) (gradient u x) (gradient ψ x) +
      inner (𝕜 := ℝ) (V x)
        (gradient (fun y => inner (𝕜 := ℝ) (gradient u y) (gradient ψ y)) x) -
      inner (𝕜 := ℝ) (gradient u x)
        (gradient (fun y => inner (𝕜 := ℝ) (V y) (gradient ψ y)) x) := by
  have hgu := WeakHarmonicRegularity.gradient_contDiff hu
  have hgψ := WeakHarmonicRegularity.gradient_contDiff hψ
  have hs : inner (𝕜 := ℝ) (V x)
      (gradient (fun y => inner (𝕜 := ℝ) (gradient u y) (gradient ψ y)) x) =
      inner (𝕜 := ℝ) (gradient u x) (fderiv ℝ (gradient ψ) x (V x)) +
        inner (𝕜 := ℝ) (fderiv ℝ (gradient u) x (V x)) (gradient ψ x) := by
    rw [real_inner_comm, ← fderiv_apply_eq_inner_gradient,
      fderiv_inner_apply ℝ ((hgu.differentiable (by simp)) x)
        ((hgψ.differentiable (by simp)) x)]
  rw [hs, gradient_inner_gradient hV hu, gradient_inner_gradient hV hψ]
  simp only [energyVariationOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    inner_add_left, inner_add_right, inner_sub_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  ring

/-- The exact compact-test Eulerian commutator for a genuine smooth
Poisson function. Its Laplacian is used only on the actual test support. -/
theorem eulerian_commutator_smooth_test {D : Set Plane} {V : Plane → Plane}
    {u ψ : Plane → ℝ} (hV : ContDiff ℝ ∞ V) (hu : ContDiff ℝ ∞ u)
    (hψ : IsTest D ψ)
    (hlap : ∀ x ∈ tsupport ψ, WeakHarmonicRegularity.planarLaplacian u x = -1) :
    (∫ x, inner (𝕜 := ℝ)
      (gradient (fun y => inner (𝕜 := ℝ) (V y) (gradient u y)) x) (gradient ψ x)) =
      (∫ x, divergence V x * ψ x) -
        ∫ x, inner (𝕜 := ℝ) (energyVariationOperator V x (gradient u x)) (gradient ψ x) := by
  let f : Plane → ℝ := fun x => inner (𝕜 := ℝ) (V x) (gradient ψ x)
  let S : Plane → ℝ := fun x => inner (𝕜 := ℝ) (gradient u x) (gradient ψ x)
  have hgu := WeakHarmonicRegularity.gradient_contDiff hu
  have hf : IsTest D f := IsTest_inner_gradient hψ hV
  have hS : IsTest D S := IsTest_inner_gradient hψ hgu
  have hP : (∫ x, inner (𝕜 := ℝ) (gradient u x) (gradient f x)) = ∫ x, f x := by
    rw [classical_laplacian_smooth_test_equation isOpen_univ hu.contDiffOn
      (hf.mono (subset_univ D))]
    have heq : (fun x => WeakHarmonicRegularity.planarLaplacian u x * f x) = fun x => -f x := by
      funext x
      by_cases hx : x ∈ tsupport ψ
      · rw [hlap x hx, neg_one_mul]
      · simp only [f, gradient_eq_zero_of_not_mem_tsupport hx, inner_zero_right, mul_zero, neg_zero]
    rw [heq, integral_neg, neg_neg]
  have hdivS := divergence_smooth_test_pairing hV hS
  have hdivψ := divergence_smooth_test_pairing hV hψ
  have hA : Continuous (fun x => energyVariationOperator V x (gradient u x)) := by
    have hd := hV.continuous_fderiv (by simp)
    exact (((divergence_continuous hV).smul hgu.continuous).sub
      (hd.clm_apply hgu.continuous)).sub
      ((ContinuousLinearMap.adjoint.continuous.comp hd).clm_apply hgu.continuous)
  have hIw := integral_compact_inner_gradient
    (WeakHarmonicRegularity.gradient_contDiff (hV.inner ℝ hgu)).continuous hψ
  have hIa := integral_compact_inner_gradient hA hψ
  have hIdS : Integrable (fun x => divergence V x * S x) :=
    ((divergence_continuous hV).mul hS.1.continuous).integrable_of_hasCompactSupport hS.2.1.mul_left
  have hIadv := integral_compact_inner_gradient hV.continuous hS
  have hIp := integral_compact_inner_gradient hgu.continuous hf
  have hidentity := integral_congr_ae (ae_of_all volume (eulerian_commutator_pointwise hV hu hψ.1))
  change (∫ x, inner (𝕜 := ℝ)
      (gradient (fun y => inner (𝕜 := ℝ) (V y) (gradient u y)) x) (gradient ψ x) +
      inner (𝕜 := ℝ) (energyVariationOperator V x (gradient u x)) (gradient ψ x)) =
    (∫ x, divergence V x * S x + inner (𝕜 := ℝ) (V x) (gradient S x) -
      inner (𝕜 := ℝ) (gradient u x) (gradient f x)) at hidentity
  have hsum := integral_add hIdS hIadv
  have hsub := integral_sub (hIdS.add hIadv) hIp
  simp only [Pi.add_apply] at hsum hsub
  rw [integral_add hIw hIa, hsub, hsum] at hidentity
  change _ + _ = _ + _ - _ at hidentity
  change (∫ x, divergence V x * S x) = -(∫ x, inner (𝕜 := ℝ) (V x) (gradient S x)) at hdivS
  change (∫ x, divergence V x * ψ x) = -(∫ x, f x) at hdivψ
  linarith

/-- The commutator uses only actual interior smoothness of the Poisson
function. A genuine compact cutoff removes any global smoothness or boundary
extension requirement. This is the form applicable to the Cauchy torsion. -/
theorem eulerian_commutator_local_smooth_test {D : Set Plane} {V : Plane → Plane}
    {u ψ : Plane → ℝ} (hD : IsOpen D) (hV : ContDiff ℝ ∞ V)
    (hu : ContDiffOn ℝ ∞ u D)
    (hlap : ∀ x ∈ D, WeakHarmonicRegularity.planarLaplacian u x = -1)
    (hψ : IsTest D ψ) :
    (∫ x, inner (𝕜 := ℝ)
      (gradient (fun y => inner (𝕜 := ℝ) (V y) (gradient u y)) x) (gradient ψ x)) =
      (∫ x, divergence V x * ψ x) -
        ∫ x, inner (𝕜 := ℝ) (energyVariationOperator V x (gradient u x)) (gradient ψ x) := by
  obtain ⟨η, hη, hone⟩ := exists_test_eq_one_near_compact hD hψ.2.1 hψ.2.2
  let u₀ : Plane → ℝ := fun x => η x * u x
  have hu₀ : IsTest D u₀ := hη.mul_contDiffOn hD hu
  have heq {x : Plane} (hx : x ∈ tsupport ψ) : u₀ =ᶠ[𝓝 x] u := by
    have hηone := hone.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hηone] with y hy
    simp only [u₀, hy, one_mul]
  have hconv {x : Plane} (hx : x ∈ tsupport ψ) :
      (fun y => inner (𝕜 := ℝ) (V y) (gradient u₀ y)) =ᶠ[𝓝 x]
        (fun y => inner (𝕜 := ℝ) (V y) (gradient u y)) := by
    filter_upwards [(heq hx).gradient] with y hy
    rw [hy]
  have hlap₀ (x : Plane) (hx : x ∈ tsupport ψ) :
      WeakHarmonicRegularity.planarLaplacian u₀ x = -1 := by
    unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
    rw [(heq hx).gradient.fderiv_eq]
    exact hlap x (hψ.2.2 hx)
  have h := eulerian_commutator_smooth_test hV hu₀.1 hψ hlap₀
  have hleft : (∫ x, inner (𝕜 := ℝ)
      (gradient (fun y => inner (𝕜 := ℝ) (V y) (gradient u₀ y)) x) (gradient ψ x)) =
      ∫ x, inner (𝕜 := ℝ)
        (gradient (fun y => inner (𝕜 := ℝ) (V y) (gradient u y)) x) (gradient ψ x) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport ψ
      · rw [(hconv hx).gradient_eq]
      · simp [gradient_eq_zero_of_not_mem_tsupport hx]
  have hright : (∫ x, inner (𝕜 := ℝ) (energyVariationOperator V x (gradient u₀ x)) (gradient ψ x)) =
      ∫ x, inner (𝕜 := ℝ) (energyVariationOperator V x (gradient u x)) (gradient ψ x) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport ψ
      · rw [(heq hx).gradient_eq]
      · simp [gradient_eq_zero_of_not_mem_tsupport hx]
  rwa [hleft, hright] at h

/-- The actual differentiated material equation, once constructed, cancels
the proved convective commutator. This concludes the interior Eulerian
compact-test equation, without assuming a shape derivative or a boundary
trace as an extra premise. -/
theorem eulerian_smooth_test_equation_of_material_equation
    {D : Set Plane} {V : Plane → Plane} {u : Plane → ℝ} {m : Plane → Plane}
    (hD : IsOpen D) (hV : ContDiff ℝ ∞ V) (hu : ContDiffOn ℝ ∞ u D)
    (hlap : ∀ x ∈ D, WeakHarmonicRegularity.planarLaplacian u x = -1)
    (hm : MemLp m 2 volume)
    (hmaterial : ∀ ψ : Plane → ℝ, IsTest D ψ →
      (∫ x, inner (𝕜 := ℝ) (m x) (gradient ψ x)) =
        (∫ x, divergence V x * ψ x) -
          ∫ x, inner (𝕜 := ℝ) (energyVariationOperator V x (gradient u x)) (gradient ψ x))
    {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    (∫ x, inner (𝕜 := ℝ)
      (m x - gradient (fun y => inner (𝕜 := ℝ) (V y) (gradient u y)) x) (gradient ψ x)) = 0 := by
  have hconv : ContDiffOn ℝ ∞ (fun y => inner (𝕜 := ℝ) (V y) (gradient u y)) D :=
    hV.contDiffOn.inner ℝ (contDiffOn_gradient_of_isOpen hu hD)
  have hi := integrable_real_inner_of_memLp_two hm (hψ.memLp_gradient (p := 2))
  have hj := classical_smooth_test_pairing_integrable hD hconv hψ
  simp only [inner_sub_left]
  rw [integral_sub hi hj, hmaterial ψ hψ,
    eulerian_commutator_local_smooth_test hD hV hu hlap hψ, sub_self]

/-- Cutting the convection off strictly inside the domain gives a genuine
global Sobolev pair and an actual `IsWeakHarmonicOn` instance on the smaller
region. No global H¹ extension of the nonzero Eulerian boundary trace is
silently assumed. -/
theorem exists_localized_eulerian_weakHarmonic
    {D U : Set Plane} {V : Plane → Plane} {u w : Plane → ℝ} {m : Plane → Plane}
    (hD : IsOpen D) (hV : ContDiff ℝ ∞ V) (hu : ContDiffOn ℝ ∞ u D)
    (hlap : ∀ x ∈ D, WeakHarmonicRegularity.planarLaplacian u x = -1)
    (hw : MemH10 D w m) (_hU : IsOpen U) (hUc : IsCompact (closure U)) (hUD : closure U ⊆ D)
    (hmaterial : ∀ ψ : Plane → ℝ, IsTest D ψ →
      (∫ x, inner (𝕜 := ℝ) (m x) (gradient ψ x)) =
        (∫ x, divergence V x * ψ x) -
          ∫ x, inner (𝕜 := ℝ) (energyVariationOperator V x (gradient u x)) (gradient ψ x)) :
    ∃ c : Plane → ℝ, IsTest D c ∧
      (∀ x ∈ U, c x = inner (𝕜 := ℝ) (V x) (gradient u x)) ∧
      IsWeakHarmonicOn U (fun x => w x - c x) (fun x => m x - gradient c x) := by
  let f : Plane → ℝ := fun y => inner (𝕜 := ℝ) (V y) (gradient u y)
  have hf : ContDiffOn ℝ ∞ f D :=
    hV.contDiffOn.inner ℝ (contDiffOn_gradient_of_isOpen hu hD)
  obtain ⟨η, hη, hone⟩ := exists_test_eq_one_near_compact hD hUc hUD
  let c : Plane → ℝ := fun x => η x * f x
  have hc : IsTest D c := hη.mul_contDiffOn hD hf
  have heq {x : Plane} (hx : x ∈ U) : c =ᶠ[𝓝 x] f := by
    have hηone := hone.filter_mono (nhds_le_nhdsSet (subset_closure hx))
    filter_upwards [hηone] with y hy
    simp only [c, hy, one_mul]
  refine ⟨c, hc, fun x hx => (heq hx).self_of_nhds, (hw.sub hc.memH10).distributionalGradient, ?_⟩
  intro ψ hψ
  have ht := eulerian_smooth_test_equation_of_material_equation hD hV hu hlap hw.2.1
    hmaterial (hψ.mono (subset_closure.trans hUD))
  convert ht using 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    by_cases hx : x ∈ U
    · rw [(heq hx).gradient_eq]
    · simp [gradient_eq_zero_of_not_mem_tsupport (fun hs => hx (hψ.2.2 hs))]

end Torsion.Shape

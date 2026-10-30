module

public import Torsion.WeakGradient
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Convolution

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual smoothing of the concrete distributional weak gradient

These are smoothing theorems, not an assertion of Weyl's lemma. In particular
this module does not yet identify a weak harmonic function with one fixed
smooth representative. It proves that smoothing commutes with the actual
weak gradient and supplies smooth approximation machinery for that remaining
regularity argument.
-/

noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ENNReal NNReal ContDiff Convolution

namespace Torsion.WeakHarmonicRegularity

/-- Scalar convolution with a smooth compactly supported kernel. -/
def mollify (u κ : Plane → ℝ) : Plane → ℝ :=
  u ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ

/-- Convolution of the actual weak vector gradient by the same scalar kernel. -/
def mollifyGradient (g : Plane → Plane) (κ : Plane → ℝ) : Plane → Plane :=
  g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Plane →L[ℝ] Plane).flip, volume] κ

/-- Every fixed smooth compact kernel gives a genuinely smooth function. -/
theorem mollify_contDiff {u κ : Plane → ℝ} (hu : MemLp u 2 volume)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) : ContDiff ℝ ∞ (mollify u κ) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (hu.locallyIntegrable (by norm_num)) hκ

/-- The vector convolutions are smooth as well. -/
theorem mollifyGradient_contDiff {g : Plane → Plane} {κ : Plane → ℝ}
    (hg : MemLp g 2 volume) (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) :
    ContDiff ℝ ∞ (mollifyGradient g κ) :=
  hc.contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Plane →L[ℝ] Plane).flip
    (hg.locallyIntegrable (by norm_num)) hκ

private def subHomeomorph (x : Plane) : Plane ≃ₜ Plane where
  toFun y := x - y
  invFun y := x - y
  left_inv y := by simp only [sub_sub_cancel]
  right_inv y := by simp only [sub_sub_cancel]
  continuous_toFun := continuous_const.sub continuous_id
  continuous_invFun := continuous_const.sub continuous_id

private theorem translated_fderiv {κ : Plane → ℝ} (hκ : Differentiable ℝ κ)
    (x y v : Plane) :
    fderiv ℝ (fun t => κ (x - t)) y v = - fderiv ℝ κ (x - y) v := by
  have h := (hκ (x - y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  change (fderiv ℝ (κ ∘ HSub.hSub x) y) v = _
  rw [h.fderiv]
  simp

/-- The actual distributional integration-by-parts identity moves derivatives
from a translated smoothing kernel to the weak gradient. -/
theorem kernel_integration_by_parts {u κ : Plane → ℝ} {g : Plane → Plane}
    (hgrad : HasDistributionalGradient u g)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x v : Plane) :
    (∫ t, u t * fderiv ℝ κ (x - t) v) =
      ∫ t, inner (𝕜 := ℝ) (g t) v * κ (x - t) := by
  have htest : ContDiff ℝ ∞ (fun t => κ (x - t)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have hcompact : HasCompactSupport (fun t => κ (x - t)) :=
    hc.comp_homeomorph (subHomeomorph x)
  have h := hgrad (fun t => κ (x - t)) htest hcompact v
  simp_rw [translated_fderiv (hκ.differentiable (by simp)), mul_neg] at h
  rw [integral_neg] at h
  exact neg_injective h

/-- Smoothing commutes with the weak gradient, as an actual pointwise
classical gradient identity. No regularity of the weak representative is
assumed. -/
theorem mollify_hasGradientAt {u κ : Plane → ℝ} {g : Plane → Plane}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hgrad : HasDistributionalGradient u g)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x : Plane) :
    HasGradientAt (mollify u κ) (mollifyGradient g κ x) x := by
  have hderiv := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (hu.locallyIntegrable (by norm_num)) (hκ.of_le (by simp)) x
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hderiv using 1
  · rfl
  ext v
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ)
    (hu.locallyIntegrable (by norm_num)) (hc.fderiv ℝ) (hκ.continuous_fderiv (by simp))]
  change inner (𝕜 := ℝ) (mollifyGradient g κ x) v =
    ∫ t, u t * fderiv ℝ κ (x - t) v
  rw [kernel_integration_by_parts hgrad hκ hc]
  have hi : Integrable (fun t => κ (x - t) • g t) volume :=
    hc.convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Plane →L[ℝ] Plane).flip
      (hg.locallyIntegrable (by norm_num)) hκ.continuous x
  change inner (𝕜 := ℝ) (∫ t, κ (x - t) • g t) v = _
  calc
    inner (𝕜 := ℝ) (∫ t, κ (x - t) • g t) v =
        inner (𝕜 := ℝ) v (∫ t, κ (x - t) • g t) := real_inner_comm _ _
    _ = ∫ t, inner (𝕜 := ℝ) v (κ (x - t) • g t) := (integral_inner hi v).symm
    _ = ∫ t, inner (𝕜 := ℝ) (g t) v * κ (x - t) := by
      apply integral_congr_ae
      exact ae_of_all _ fun t => by
        simp only [real_inner_smul_right]
        rw [real_inner_comm]
        ring

/-- Applied to the originally defined H¹₀ pairs, the smoothed classical
gradient is exactly the convolution of their supplied weak gradient. -/
theorem MemH10_mollify_gradient {D : Set Plane} {u κ : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x : Plane) :
    gradient (mollify u κ) x = mollifyGradient g κ x :=
  (mollify_hasGradientAt hu.1 hu.2.1 hu.distributionalGradient hκ hc x).gradient

/-- The planar divergence, using the real orthonormal directions `1` and `I`. -/
def planarDivergence (F : Plane → Plane) (x : Plane) : ℝ :=
  (fderiv ℝ F x (1 : Plane)).re + (fderiv ℝ F x Complex.I).im

/-- The classical planar Laplacian, defined as divergence of the gradient. -/
def planarLaplacian (f : Plane → ℝ) (x : Plane) : ℝ := planarDivergence (gradient f) x

/-- The divergence of a smoothed vector field is the actual integral of its
pairing with the differentiated kernel. -/
theorem divergence_mollifyGradient {g : Plane → Plane} {κ : Plane → ℝ}
    (hg : MemLp g 2 volume) (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x : Plane) :
    planarDivergence (mollifyGradient g κ) x =
      ∫ t, inner (𝕜 := ℝ) (g t) (gradient κ (x - t)) := by
  let L : Plane →L[ℝ] ℝ →L[ℝ] Plane :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Plane →L[ℝ] Plane).flip
  have hderiv := hc.hasFDerivAt_convolution_right L
    (hg.locallyIntegrable (by norm_num)) (hκ.of_le (by simp)) x
  have hdir (v : Plane) : fderiv ℝ (mollifyGradient g κ) x v =
      ∫ t, fderiv ℝ κ (x - t) v • g t := by
    change fderiv ℝ (g ⋆[L, volume] κ) x v = _
    rw [hderiv.fderiv, convolution_precompR_apply L
      (hg.locallyIntegrable (by norm_num)) (hc.fderiv ℝ) (hκ.continuous_fderiv (by simp))]
    rfl
  have hi : Integrable (fun t => L.precompR Plane (g t) (fderiv ℝ κ (x - t))) volume :=
    (hc.fderiv ℝ).convolutionExists_right (L.precompR Plane)
      (hg.locallyIntegrable (by norm_num)) (hκ.continuous_fderiv (by simp)) x
  have hiv (v : Plane) : Integrable (fun t => fderiv ℝ κ (x - t) v • g t) volume :=
    (ContinuousLinearMap.apply ℝ Plane v).integrable_comp hi
  unfold planarDivergence
  rw [hdir, hdir]
  have hre : (∫ t, fderiv ℝ κ (x - t) (1 : Plane) • g t).re =
      ∫ t, (fderiv ℝ κ (x - t) (1 : Plane) • g t).re := (integral_re (hiv 1)).symm
  have him : (∫ t, fderiv ℝ κ (x - t) Complex.I • g t).im =
      ∫ t, (fderiv ℝ κ (x - t) Complex.I • g t).im := (integral_im (hiv Complex.I)).symm
  have hire : Integrable (fun t => (fderiv ℝ κ (x - t) (1 : Plane) • g t).re) volume := (hiv 1).re
  have hiim : Integrable (fun t => (fderiv ℝ κ (x - t) Complex.I • g t).im) volume := (hiv Complex.I).im
  rw [hre, him, ← integral_add hire hiim]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    simp [fderiv_apply_eq_inner_gradient, Complex.inner, Complex.mul_re, mul_comm, -inner_gradient_left]

private theorem gradient_translated {κ : Plane → ℝ} (hκ : Differentiable ℝ κ)
    (x y : Plane) : gradient (fun t => κ (x - t)) y = -gradient κ (x - y) := by
  have hd : fderiv ℝ (fun t => κ (x - t)) y = - fderiv ℝ κ (x - y) := by
    ext v
    exact translated_fderiv hκ x y v
  simp only [gradient, hd, map_neg]

/-- Smoothing a weakly harmonic pair produces a genuinely smooth classically
harmonic function wherever the translated kernel is supported in the region.
This is the harmonic-smoothing step of Weyl's argument, not the assertion
that all these smoothings coincide with a single representative. -/
theorem mollify_laplacian_eq_zero {U : Set Plane} {u κ : Plane → ℝ} {g : Plane → Plane}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume) (hw : IsWeakHarmonicOn U u g)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x : Plane)
    (hsupp : tsupport (fun t => κ (x - t)) ⊆ U) :
    planarLaplacian (mollify u κ) x = 0 := by
  have hgrad : gradient (mollify u κ) = mollifyGradient g κ :=
    funext fun y => (mollify_hasGradientAt hu hg hw.1 hκ hc y).gradient
  unfold planarLaplacian
  rw [hgrad, divergence_mollifyGradient hg hκ hc]
  have htest : IsTest U (fun t => κ (x - t)) :=
    ⟨hκ.comp (contDiff_const.sub contDiff_id), hc.comp_homeomorph (subHomeomorph x), hsupp⟩
  have heq := hw.2 _ htest
  simp_rw [gradient_translated (hκ.differentiable (by simp)), inner_neg_right] at heq
  rw [integral_neg] at heq
  exact neg_eq_zero.mp heq

/-- An explicit family of smooth kernels with radii `1/(n+1)` and `2/(n+1)`. -/
def shrinkingBump (n : ℕ) : ContDiffBump (0 : Plane) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    exact (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2 (by norm_num)

/-- Each actual smoothing kernel has total integral one. -/
def mollifier (n : ℕ) : Plane → ℝ := (shrinkingBump n).normed volume

/-- A concrete smooth approximating sequence. -/
def smoothApprox (u : Plane → ℝ) (n : ℕ) : Plane → ℝ := mollify u (mollifier n)

theorem smoothApprox_contDiff {u : Plane → ℝ} (hu : MemLp u 2 volume) (n : ℕ) :
    ContDiff ℝ ∞ (smoothApprox u n) :=
  mollify_contDiff hu (shrinkingBump n).contDiff_normed (shrinkingBump n).hasCompactSupport_normed

private theorem shrinkingBump_rOut_tendsto :
    Tendsto (fun n : ℕ => (shrinkingBump n).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump, mul_one_div, mul_zero] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)

private theorem shrinkingBump_ratio :
    ∀ᶠ n : ℕ in atTop, (shrinkingBump n).rOut ≤ 2 * (shrinkingBump n).rIn := by
  apply Eventually.of_forall
  intro n
  dsimp [shrinkingBump]
  rw [mul_one_div]

private theorem mollify_eq_kernel_convolution (u κ : Plane → ℝ) :
    mollify u κ = κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := by
  have hL : (ContinuousLinearMap.mul ℝ ℝ).flip =
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm _ _
  unfold mollify
  rw [← convolution_flip, hL]

/-- The explicit smooth approximants converge to the actual value almost
everywhere, by the Lebesgue differentiation theorem for shrinking bumps. -/
theorem ae_smoothApprox_tendsto {u : Plane → ℝ} (hu : MemLp u 2 volume) :
    ∀ᵐ x ∂volume, Tendsto (fun n => smoothApprox u n x) atTop (𝓝 (u x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    shrinkingBump_rOut_tendsto shrinkingBump_ratio (hu.locallyIntegrable (by norm_num))
  simpa only [smoothApprox, mollifier, mollify_eq_kernel_convolution] using h

/-- The gradients of those same approximants converge almost everywhere to
the supplied actual weak gradient. This is a genuine approximation result;
it does not yet supply a single smooth representative of a harmonic limit. -/
theorem ae_gradient_smoothApprox_tendsto {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hgrad : HasDistributionalGradient u g) :
    ∀ᵐ x ∂volume, Tendsto (fun n => gradient (smoothApprox u n) x) atTop (𝓝 (g x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    shrinkingBump_rOut_tendsto shrinkingBump_ratio (hg.locallyIntegrable (by norm_num))
  filter_upwards [h] with x hx
  have hconv (n : ℕ) : gradient (smoothApprox u n) x =
      ((shrinkingBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
    rw [show gradient (smoothApprox u n) x = mollifyGradient g (mollifier n) x from
      (mollify_hasGradientAt hu hg hgrad (shrinkingBump n).contDiff_normed
        (shrinkingBump n).hasCompactSupport_normed x).gradient]
    exact congrFun (convolution_flip (L := ContinuousLinearMap.lsmul ℝ ℝ)) x
  simpa only [hconv] using hx

end Torsion.WeakHarmonicRegularity

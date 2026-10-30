import Torsion.RestrictedSpectralAnalyticHeight
import Torsion.CauchyBoundaryStationarity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Smooth extension of the actual inverse across the open free arc

The already-proved spectral analytic continuation has nonzero derivative.
Its actual local inverse agrees with the constructed physical inverse on
an interior neighborhood of the boundary point. This supplies full local
regularity at the displaced patch, independently of either junction.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral

theorem IsRestrictedEigenfunction.exists_smooth_chart_at_freeArc
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ∃ (r : ℝ) (A K : Plane → Plane), 0 < r ∧
      DifferentiableOn ℂ A (Metric.ball (t : Plane) r) ∧
      EqOn A (cauchy φ) (Metric.ball (t : Plane) r ∩ upperHalfPlane) ∧
      ContDiffAt ℂ ∞ K (cauchyExtension φ (t : Plane)) ∧
      K (cauchyExtension φ (t : Plane)) = (t : Plane) ∧
      K =ᶠ[𝓝[cauchyImage φ] (cauchyExtension φ (t : Plane))] cauchyInverse φ := by
  obtain ⟨r, hr, A, hAd, hA⟩ := hEig.exists_height_Cauchy_extension_of_odd hodd t ht
  have hAt : A (t : Plane) = cauchyExtension φ (t : Plane) :=
    hA ⟨Metric.mem_ball_self hr, by simp⟩
  have hAa : AnalyticAt ℂ A (t : Plane) := hAd.analyticAt (Metric.ball_mem_nhds _ hr)
  have hreal : (fun s : ℝ => A (s : Plane)) =ᶠ[𝓝 t]
      (fun s : ℝ => cauchyExtension φ (s : Plane)) := by
    filter_upwards [Metric.ball_mem_nhds t hr] with s hs
    apply hA
    refine ⟨?_, by simp⟩
    simpa only [Metric.mem_ball, Complex.isometry_ofReal.dist_eq] using hs
  have hdA : deriv A (t : Plane) = cauchyDerivativeExtension φ (t : Plane) :=
    hAa.differentiableAt.hasDerivAt.comp_ofReal.unique
      ((cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero t).congr_of_eventuallyEq hreal)
  have hne : deriv A (t : Plane) ≠ 0 := by
    rw [hdA]
    exact cauchyDerivativeExtension_ne_zero_on_interval ha hφ hα0 hα1 hodd hzero hpos
      hlinear (Ioo_subset_Icc_self ht)
  have hstrict := hAa.hasStrictFDerivAt.hasStrictDerivAt.hasStrictFDerivAt_equiv hne
  have hcd : ContDiffAt ℂ ∞ A (t : Plane) := hAa.contDiffAt
  let K := hcd.localInverse hstrict.hasFDerivAt (by simp)
  have hK : ContDiffAt ℂ ∞ K (A (t : Plane)) :=
    hcd.to_localInverse hstrict.hasFDerivAt (by simp)
  have hKAt : K (A (t : Plane)) = (t : Plane) :=
    hcd.localInverse_apply_image hstrict.hasFDerivAt (by simp)
  have hleft : ∀ᶠ z in 𝓝 (t : Plane), K (A z) = z :=
    (hcd.hasStrictFDerivAt' hstrict.hasFDerivAt (by simp)).eventually_left_inverse
  refine ⟨r, A, K, hr, hAd, ?_, hAt ▸ hK, hAt ▸ hKAt, ?_⟩
  · intro z hz
    change A z = cauchy φ z
    rw [show A z = cauchyExtension φ z from
      hA ⟨hz.1, (show 0 < z.im from hz.2).le⟩,
      cauchyExtension_eq (hφ.continuous hα0).continuousOn hz.2]
  · have hinv := cauchyInverse_boundary_tendsto hφ hα0 hα1 hodd hzero hpos t
    filter_upwards [hinv.eventually (Metric.ball_mem_nhds _ hr),
      hinv.eventually hleft, self_mem_nhdsWithin] with w hw hKw hwD
    have hAw : A (cauchyInverse φ w) = w := by
      rw [show A (cauchyInverse φ w) = cauchyExtension φ (cauchyInverse φ w) from
        hA ⟨hw, (show 0 < (cauchyInverse φ w).im from cauchyInverse_mem hwD).le⟩,
        cauchyExtension_eq (hφ.continuous hα0).continuousOn (cauchyInverse_mem hwD),
        cauchy_cauchyInverse hwD]
    rwa [hAw] at hKw

theorem IsRestrictedEigenfunction.exists_smooth_inverse_at_freeArc
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ∃ K : Plane → Plane,
      ContDiffAt ℂ ∞ K (cauchyExtension φ (t : Plane)) ∧
      K (cauchyExtension φ (t : Plane)) = (t : Plane) ∧
      K =ᶠ[𝓝[cauchyImage φ] (cauchyExtension φ (t : Plane))] cauchyInverse φ := by
  obtain ⟨r, A, K, hr, hAd, hA, hK, hKt, hKeq⟩ :=
    hEig.exists_smooth_chart_at_freeArc ha hφ hα0 hα1 hodd hzero hpos hlinear ht
  exact ⟨K, hK, hKt, hKeq⟩

end Torsion.Spectral

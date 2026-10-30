module

public import Torsion.CauchyFreeArcGradient

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Constructed compact smooth Eulerian boundary data

A compact smooth displacement supported above the flat boundary produces
actual compact smooth data in the original conformal parameter. In
particular no smoothness at the two junctions is needed.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral

theorem IsRestrictedEigenfunction.cauchyBoundary_contDiffAt
    {a : ℝ} {φ : ℝ → ℝ} (hEig : IsRestrictedEigenfunction a φ)
    (hodd : Function.Odd φ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun s : ℝ => cauchyExtension φ (s : Plane)) t := by
  obtain ⟨r, hr, A, hAd, hA⟩ := hEig.exists_height_Cauchy_extension_of_odd hodd t ht
  have hAa : AnalyticAt ℂ A (t : Plane) := hAd.analyticAt (Metric.ball_mem_nhds _ hr)
  apply (((hAa.contDiffAt.restrict_scalars ℝ).comp t
    Complex.ofRealCLM.contDiff.contDiffAt)).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds t hr] with s hs
  symm
  apply hA
  refine ⟨?_, by simp⟩
  simpa only [Metric.mem_ball, Complex.isometry_ofReal.dist_eq] using hs

theorem IsRestrictedEigenfunction.cauchyBoundaryDerivative_contDiffAt
    {a : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun s : ℝ => cauchyDerivativeExtension φ (s : Plane)) t := by
  have hf := hEig.cauchyBoundary_contDiffAt hodd ht
  have hd := (hf.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiffAt_const (c := (1 : ℝ)))
  have heq : (fun s : ℝ => fderiv ℝ (fun s : ℝ => cauchyExtension φ (s : Plane)) s 1) =
      (fun s : ℝ => cauchyDerivativeExtension φ (s : Plane)) := by
    funext s
    exact (cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero s).deriv
  rw [heq] at hd
  exact hd

/-- The actual negative convective trace in conformal boundary coordinates. -/
def shapeBoundaryData (a : ℝ) (φ : ℝ → ℝ) (V : Plane → Plane) (t : ℝ) : ℝ :=
  -inner (𝕜 := ℝ) (V (cauchyExtension φ (t : Plane)))
    (Complex.I * cauchyDerivativeExtension φ (t : Plane) / ((2 * a : ℝ) : Plane))

private theorem shapeBoundaryData_eventually_zero {a : ℝ} {φ : ℝ → ℝ}
    {C α : ℝ≥0} (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {V : Plane → Plane} (hVU : tsupport V ⊆ upperHalfPlane)
    {t : ℝ} (ht : t ∉ Ioo (-1 : ℝ) 1) :
    shapeBoundaryData a φ V =ᶠ[𝓝 t] 0 := by
  have habs : 1 ≤ |t| := by
    simp only [mem_Ioo, not_and_or, not_lt] at ht
    rcases ht with ht | ht
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · exact (le_abs_self t).trans' ht
  have hy : (cauchyExtension φ (t : Plane)).im = 0 := by
    simp [cauchyExtension_ofReal, height_zero_of_one_le_abs φ habs]
  have hn : cauchyExtension φ (t : Plane) ∉ tsupport V := by
    intro h
    have hpos : 0 < (cauchyExtension φ (t : Plane)).im := hVU h
    simpa only [hy, lt_self_iff_false] using hpos
  have hVzero : V =ᶠ[𝓝 (cauchyExtension φ (t : Plane))] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hn
  have hF := (cauchy_boundary_contDiff_one hφ hα0 hα1 hodd hzero).continuous.tendsto t
  filter_upwards [hF.eventually hVzero] with s hs
  simp [shapeBoundaryData, hs]

/-- Compact smooth physical displacements give compact smooth conformal
boundary data, with support strictly inside the free parameter interval. -/
theorem IsRestrictedEigenfunction.shapeBoundaryData_smooth_compact
    {a : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVU : tsupport V ⊆ upperHalfPlane) :
    ContDiff ℝ ∞ (shapeBoundaryData a φ V) ∧
      HasCompactSupport (shapeBoundaryData a φ V) ∧
      tsupport (shapeBoundaryData a φ V) ⊆ Ioo (-1 : ℝ) 1 := by
  have hsupp : tsupport (shapeBoundaryData a φ V) ⊆ Ioo (-1 : ℝ) 1 := by
    intro t ht
    by_contra hn
    exact (notMem_tsupport_iff_eventuallyEq.mpr
      (shapeBoundaryData_eventually_zero hφ hα0 hα1 hodd hzero hVU hn)) ht
  refine ⟨contDiff_iff_contDiffAt.mpr (fun t => ?_), ?_, hsupp⟩
  · by_cases ht : t ∈ Ioo (-1 : ℝ) 1
    · have hF := hEig.cauchyBoundary_contDiffAt hodd ht
      have hD := hEig.cauchyBoundaryDerivative_contDiffAt hφ hα0 hα1 hodd hzero ht
      exact ((hV.contDiffAt.comp t hF).inner ℝ
        (contDiffAt_const.mul hD |>.div_const _)).neg
    · exact contDiffAt_const.congr_of_eventuallyEq
        (shapeBoundaryData_eventually_zero hφ hα0 hα1 hodd hzero hVU ht)
  · exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (hsupp.trans Ioo_subset_Icc_self)

end Torsion.Spectral

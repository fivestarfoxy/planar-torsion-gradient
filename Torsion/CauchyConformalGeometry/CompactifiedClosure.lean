module

public import Torsion.CauchyConformalGeometry.InverseBoundary
public import Torsion.CauchyConformalGeometry.CompactifiedBoundary

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual compactified closed-half-plane homeomorphism

The continuous Cauchy extension and the value zero at infinity define a
map on the one-point compactification of the concrete closed half-plane.
Its continuity, injectivity and exact closed-image range are proved here.
The resulting homeomorphism includes the actual interior map and the
complete finite and infinite boundary parametrization.
-/
noncomputable section
open Set Filter MeasureTheory Bornology
open scoped Topology NNReal OnePoint

namespace Torsion.Spectral

/-- The concrete closed parameter half-plane, with its subtype topology. -/
abbrev CauchyClosedHalfPlane := {z : ℂ // 0 ≤ z.im}

/-- The actual closed-half-plane map, with zero at its single point at infinity. -/
def cauchyCompactifiedClosure (φ : ℝ → ℝ) (z : OnePoint CauchyClosedHalfPlane) : ℂ :=
  z.elim 0 (fun w : CauchyClosedHalfPlane => cauchyExtension φ (w : ℂ))

@[simp] theorem cauchyCompactifiedClosure_infty (φ : ℝ → ℝ) :
    cauchyCompactifiedClosure φ ∞ = 0 := rfl

@[simp] theorem cauchyCompactifiedClosure_coe (φ : ℝ → ℝ) (z : CauchyClosedHalfPlane) :
    cauchyCompactifiedClosure φ (z : OnePoint CauchyClosedHalfPlane) =
      cauchyExtension φ (z : ℂ) := rfl

/-- On the closed exterior region the genuine boundary extension agrees
with the original Cauchy integral as well as on the open half-plane. -/
theorem cauchyExtension_eq_of_closed_exterior {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {z : ℂ} (hz : 0 ≤ z.im) (hnorm : 1 < ‖z‖) :
    cauchyExtension φ z = cauchy φ z := by
  by_cases hz0 : z.im = 0
  · have hreal : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz0]
    rw [← hreal]
    apply cauchyExtension_ofReal_exterior hφ hα0 hα1 hodd hzero
    have hnorm' : 1 < ‖(z.re : ℂ)‖ := by rw [hreal]; exact hnorm
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hnorm' 
  · exact cauchyExtension_eq (hφ.continuous hα0).continuousOn
      (lt_of_le_of_ne hz (Ne.symm hz0))

/-- The genuine closed-half-plane values tend to zero in every escaping
parameter direction, including escape along the finite real boundary. -/
theorem cauchy_closedHalfPlane_tendsto_zero {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) :
    Tendsto (fun z : CauchyClosedHalfPlane => cauchyExtension φ (z : ℂ))
      (coclosedCompact CauchyClosedHalfPlane) (𝓝 0) := by
  have hs : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have hsub : Tendsto (fun z : CauchyClosedHalfPlane => (z : ℂ))
      (coclosedCompact CauchyClosedHalfPlane) (cocompact ℂ) := by
    simpa only [coclosedCompact_eq_cocompact] using hs.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have hn : Tendsto (fun z : CauchyClosedHalfPlane => ‖(z : ℂ)‖)
      (coclosedCompact CauchyClosedHalfPlane) atTop :=
    tendsto_norm_cocompact_atTop.comp hsub
  have h := cauchy_tendsto_zero (hφ.continuous hα0).continuousOn hn
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (1 : ℝ))] with z hz
  exact (cauchyExtension_eq_of_closed_exterior hφ hα0 hα1 hodd hzero z.property hz).symm

/-- Continuity at all finite parameters and at the single infinity point. -/
theorem cauchyCompactifiedClosure_continuous {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) :
    Continuous (cauchyCompactifiedClosure φ) := by
  apply (OnePoint.continuous_iff _).2
  refine ⟨cauchy_closedHalfPlane_tendsto_zero hφ hα0 hα1 hodd hzero, ?_⟩
  have hF := (cauchy_extensions_diffContOnCl_of_holder hφ hα0 hα1 hodd hzero).1.continuousOn
  have hF' : ContinuousOn (cauchyExtension φ) {z : ℂ | 0 ≤ z.im} := by
    simpa only [upperHalfPlane, Complex.closure_setOf_lt_im] using hF
  exact hF'.restrict

/-- Finite closed-half-plane parameters are not identified by the actual
extension. Interior univalence and the proved finite boundary inverse
identification handle all combinations of interior and real parameters. -/
theorem cauchyExtension_injOn_closedHalfPlane {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    InjOn (cauchyExtension φ) (closure upperHalfPlane) := by
  intro z hz w hw hzw
  have hc := hφ.continuous hα0
  have hzge : 0 ≤ z.im := by
    simpa only [upperHalfPlane, Complex.closure_setOf_lt_im, mem_setOf_eq] using hz
  have hwge : 0 ≤ w.im := by
    simpa only [upperHalfPlane, Complex.closure_setOf_lt_im, mem_setOf_eq] using hw
  by_cases hz0 : z.im = 0
  · have hreal : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz0]
    have hwz : w = (z.re : ℂ) :=
      cauchyExtension_preimage_boundary hφ hα0 hα1 hodd hzero hpos hw z.re
        (by rw [hreal]; exact hzw.symm)
    exact hreal.symm.trans hwz.symm
  by_cases hw0 : w.im = 0
  · have hreal : (w.re : ℂ) = w := by apply Complex.ext <;> simp [hw0]
    have hzw' : z = (w.re : ℂ) :=
      cauchyExtension_preimage_boundary hφ hα0 hα1 hodd hzero hpos hz w.re
        (by rw [hreal]; exact hzw)
    exact hzw'.trans hreal
  have hzH : z ∈ upperHalfPlane := lt_of_le_of_ne hzge (Ne.symm hz0)
  have hwH : w ∈ upperHalfPlane := lt_of_le_of_ne hwge (Ne.symm hw0)
  apply cauchy_injOn_upperHalfPlane hc hodd hzero hpos hzH hwH
  rw [← cauchyExtension_eq hc.continuousOn hzH,
    ← cauchyExtension_eq hc.continuousOn hwH]
  exact hzw

/-- Infinity is the only compactified parameter mapped to the marked point. -/
theorem cauchyExtension_ne_zero_closedHalfPlane {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : 0 ≤ z.im) : cauchyExtension φ z ≠ 0 := by
  by_cases hz0 : z.im = 0
  · have hreal : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz0]
    rw [← hreal]
    exact cauchy_boundary_ne_zero hφ hα0 hα1 hodd hzero hpos z.re
  · have hzH : z ∈ upperHalfPlane := lt_of_le_of_ne hz (Ne.symm hz0)
    rw [cauchyExtension_eq (hφ.continuous hα0).continuousOn hzH]
    intro heq
    have hi := cauchy_im_pos (hφ.continuous hα0).continuousOn hpos hzH
    simp only [heq, Complex.zero_im, lt_self_iff_false] at hi

/-- Complete injectivity includes interior points, finite boundary points,
and the single parameter at infinity. -/
theorem cauchyCompactifiedClosure_injective {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    Function.Injective (cauchyCompactifiedClosure φ) := by
  intro z w hzw
  induction z using OnePoint.rec with
  | infty =>
      induction w using OnePoint.rec with
      | infty => rfl
      | coe w =>
          exact False.elim (cauchyExtension_ne_zero_closedHalfPlane hφ hα0 hα1 hodd hzero hpos
            w.property hzw.symm)
  | coe z =>
      induction w using OnePoint.rec with
      | infty =>
          exact False.elim (cauchyExtension_ne_zero_closedHalfPlane hφ hα0 hα1 hodd hzero hpos
            z.property hzw)
      | coe w =>
          apply congrArg (fun v : CauchyClosedHalfPlane => (v : OnePoint CauchyClosedHalfPlane))
          apply Subtype.ext
          apply cauchyExtension_injOn_closedHalfPlane hφ hα0 hα1 hodd hzero hpos
          · simpa only [upperHalfPlane, Complex.closure_setOf_lt_im, mem_setOf_eq] using z.property
          · simpa only [upperHalfPlane, Complex.closure_setOf_lt_im, mem_setOf_eq] using w.property
          · exact hzw

/-- The complete compactified map has range exactly the actual image closure. -/
theorem range_cauchyCompactifiedClosure {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    range (cauchyCompactifiedClosure φ) = closure (cauchyImage φ) := by
  have hc := hφ.continuous hα0
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    induction z using OnePoint.rec with
    | infty => exact frontier_subset_closure (zero_mem_frontier_cauchyImage hc hodd hzero hpos)
    | coe z =>
        by_cases hz0 : (z : ℂ).im = 0
        · have hreal : (((z : ℂ).re : ℝ) : ℂ) = (z : ℂ) := by
            apply Complex.ext <;> simp [hz0]
          change cauchyExtension φ (z : ℂ) ∈ closure (cauchyImage φ)
          rw [← hreal]
          exact cauchyExtension_ofReal_mem_closure_image hc hodd hzero (z : ℂ).re
        · have hzH : (z : ℂ) ∈ upperHalfPlane := lt_of_le_of_ne z.property (Ne.symm hz0)
          rw [cauchyCompactifiedClosure_coe, cauchyExtension_eq hc.continuousOn hzH]
          exact subset_closure ⟨(z : ℂ), hzH, rfl⟩
  · rw [closure_eq_self_union_frontier, frontier_cauchyImage_eq hc hodd hzero hpos]
    rintro (⟨z, hz, rfl⟩ | (⟨t, rfl⟩ | hp))
    · refine ⟨((⟨z, (show 0 < z.im from hz).le⟩ : CauchyClosedHalfPlane) :
        OnePoint CauchyClosedHalfPlane), ?_⟩
      exact cauchyExtension_eq hc.continuousOn hz
    · exact ⟨((⟨(t : ℂ), by simp⟩ : CauchyClosedHalfPlane) :
        OnePoint CauchyClosedHalfPlane), rfl⟩
    · exact ⟨∞, (mem_singleton_iff.1 hp).symm⟩

/-- The actual compactified Cauchy map is a closed embedding. -/
theorem cauchyCompactifiedClosure_isClosedEmbedding {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    Topology.IsClosedEmbedding (cauchyCompactifiedClosure φ) :=
  (cauchyCompactifiedClosure_continuous hφ hα0 hα1 hodd hzero).isClosedEmbedding
    (cauchyCompactifiedClosure_injective hφ hα0 hα1 hodd hzero hpos)

/-- The complete actual conformal homeomorphism, including the closed
half-plane boundary and its marked infinity point. -/
def cauchyClosureHomeomorph {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    OnePoint CauchyClosedHalfPlane ≃ₜ closure (cauchyImage φ) :=
  (cauchyCompactifiedClosure_isClosedEmbedding hφ hα0 hα1 hodd hzero hpos).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_cauchyCompactifiedClosure hφ hα0 hodd hzero hpos))

@[simp] theorem cauchyClosureHomeomorph_apply_val {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) (z : OnePoint CauchyClosedHalfPlane) :
    ((cauchyClosureHomeomorph hφ hα0 hα1 hodd hzero hpos z : closure (cauchyImage φ)) : ℂ) =
      cauchyCompactifiedClosure φ z := rfl

end Torsion.Spectral

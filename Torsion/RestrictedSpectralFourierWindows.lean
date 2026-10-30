import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Compact Fourier windows in the actual full-frequency L² space

Uniform boundedness and a common Lipschitz constant give compact closure
on each compact frequency interval by Arzelà--Ascoli. Zero extension of a
continuous window function is continuous as a map into the actual global
L² space, so the truncated Fourier family has compact closure there too.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace Torsion.Spectral

/-- The concrete frequency cutoff in the full Fourier L² space. -/
def frequencyWindow (R : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  ((Lp.memLp u).indicator measurableSet_Icc).toLp ((Icc (-R) R).indicator u)

theorem frequencyWindow_ae (R : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    frequencyWindow R u =ᵐ[volume] (Icc (-R) R).indicator u :=
  MemLp.coeFn_toLp _

/-- The classical bounded-Lipschitz version of Arzelà--Ascoli, stated for
actual continuous complex-valued functions on a compact metric space. -/
theorem isCompact_closure_continuousMap_range_of_uniform_bounds
    {X ι : Type*} [MetricSpace X] [CompactSpace X]
    (F : ι → C(X, ℂ)) (B L : ℝ≥0)
    (hbound : ∀ i x, ‖F i x‖ ≤ (B : ℝ))
    (hLip : ∀ i, LipschitzWith L (F i)) : IsCompact (closure (range F)) := by
  let e : C(X, ℂ) ≃ₜ (X →ᵇ ℂ) :=
    (ContinuousMap.linearIsometryBoundedOfCompact X ℂ ℂ).toHomeomorph
  let G : ι → X →ᵇ ℂ := fun i => e (F i)
  have heq : Equicontinuous ((↑) : range G → X → ℂ) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => (L : ℝ) * t)
      (by simpa using (tendsto_const_nhds.mul (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))))
    intro x y i
    obtain ⟨j, hj⟩ := i.property
    rw [← hj]
    exact (hLip j).dist_le_mul x y
  have hK : IsCompact (closure (range G)) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) B) (isCompact_closedBall _ _)
      (range G) ?_ heq
    rintro f x ⟨i, rfl⟩
    simpa only [mem_closedBall, dist_zero_right] using hbound i x
  have himage : e.symm '' range G = range F := by
    ext f
    simp only [mem_image, mem_range, exists_exists_eq_and]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by simpa only [G, e.symm_apply_apply] using hi⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, by simp [G]⟩
  have h := hK.image e.symm.continuous
  rwa [e.symm.image_closure, himage] at h

/-- The compact parameter type for a frequency window. -/
abbrev FourierWindow (R : ℝ) := Icc (-R) R

/-- Zero extension of a continuous window function, using the canonical
constant extension only inside the indicator. -/
def zeroExtendFourierWindow (R : ℝ) (hR : 0 ≤ R) (g : C(FourierWindow R, ℂ)) : ℝ → ℂ :=
  (Icc (-R) R).indicator (ContinuousMap.IccExtend (by linarith : -R ≤ R) g)

private theorem zeroExtendFourierWindow_norm_le (R : ℝ) (hR : 0 ≤ R)
    (g : C(FourierWindow R, ℂ)) (x : ℝ) :
    ‖zeroExtendFourierWindow R hR g x‖ ≤
      ‖g‖ * ‖(Icc (-R) R).indicator (fun _ : ℝ => (1 : ℂ)) x‖ := by
  by_cases hx : x ∈ Icc (-R) R
  · simp only [zeroExtendFourierWindow, indicator_of_mem hx, norm_one, mul_one]
    exact g.norm_coe_le_norm _
  · simp [zeroExtendFourierWindow, hx]

theorem zeroExtendFourierWindow_memLp (R : ℝ) (hR : 0 ≤ R)
    (g : C(FourierWindow R, ℂ)) : MemLp (zeroExtendFourierWindow R hR g) 2 volume := by
  have hm : AEStronglyMeasurable (zeroExtendFourierWindow R hR g) volume :=
    (ContinuousMap.IccExtend (by linarith : -R ≤ R) g).continuous.aestronglyMeasurable.indicator measurableSet_Icc
  exact (memLp_indicator_const (2 : ℝ≥0∞) measurableSet_Icc (1 : ℂ)
    (Or.inr isCompact_Icc.measure_lt_top.ne)).of_le_mul hm
      (ae_of_all _ fun x => zeroExtendFourierWindow_norm_le R hR g x)

/-- Continuous window data, extended by zero, as an element of actual
full-frequency L². -/
def fourierWindowToLp (R : ℝ) (hR : 0 ≤ R) (g : C(FourierWindow R, ℂ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (zeroExtendFourierWindow_memLp R hR g).toLp (zeroExtendFourierWindow R hR g)

theorem fourierWindowToLp_ae (R : ℝ) (hR : 0 ≤ R) (g : C(FourierWindow R, ℂ)) :
    fourierWindowToLp R hR g =ᵐ[volume] zeroExtendFourierWindow R hR g :=
  MemLp.coeFn_toLp _

private theorem zeroExtendFourierWindow_sub (R : ℝ) (hR : 0 ≤ R)
    (g h : C(FourierWindow R, ℂ)) :
    zeroExtendFourierWindow R hR (g - h) =
      zeroExtendFourierWindow R hR g - zeroExtendFourierWindow R hR h := by
  funext x
  by_cases hx : x ∈ Icc (-R) R
  · simp [zeroExtendFourierWindow, hx, ContinuousMap.IccExtend, Set.IccExtend]
  · simp [zeroExtendFourierWindow, hx]

/-- Zero extension of continuous window data is continuous into the actual
global L² space, with norm controlled by the finite window measure. -/
theorem fourierWindowToLp_continuous (R : ℝ) (hR : 0 ≤ R) :
    Continuous (fourierWindowToLp R hR) := by
  let U : Lp ℂ 2 (volume : Measure ℝ) :=
    indicatorConstLp (s := Icc (-R) R) 2 measurableSet_Icc isCompact_Icc.measure_lt_top.ne (1 : ℂ)
  have hU : U =ᵐ[volume] (Icc (-R) R).indicator (fun _ : ℝ => (1 : ℂ)) :=
    indicatorConstLp_coeFn
  have hLip : LipschitzWith ‖U‖₊ (fourierWindowToLp R hR) := by
    apply LipschitzWith.of_dist_le_mul
    intro g h
    have hbound : ‖fourierWindowToLp R hR g - fourierWindowToLp R hR h‖ ≤ ‖g - h‖ * ‖U‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (fourierWindowToLp R hR g) (fourierWindowToLp R hR h),
        fourierWindowToLp_ae R hR g, fourierWindowToLp_ae R hR h, hU] with x hsub hg hh hu
      rw [hsub]
      simp only [Pi.sub_apply]
      rw [hg, hh, hu, ← Pi.sub_apply, ← zeroExtendFourierWindow_sub]
      exact zeroExtendFourierWindow_norm_le R hR (g - h) x
    simpa only [dist_eq_norm, coe_nnnorm, mul_comm] using hbound
  exact hLip.continuous

/-- The genuine continuous restriction of an actual full-frequency function. -/
def frequencyWindowRestriction (R : ℝ) (F : ℝ → ℂ) (hF : Continuous F) : C(FourierWindow R, ℂ) where
  toFun x := F x
  continuous_toFun := hF.comp continuous_subtype_val

/-- Restriction followed by zero extension agrees with the concrete L²
frequency cutoff, including the actual equivalence classes. -/
theorem fourierWindowToLp_restriction (R : ℝ) (hR : 0 ≤ R) (F : ℝ → ℂ)
    (hF : Continuous F) (hLp : MemLp F 2 volume) :
    fourierWindowToLp R hR (frequencyWindowRestriction R F hF) =
      frequencyWindow R (hLp.toLp F) := by
  apply Lp.ext
  filter_upwards [fourierWindowToLp_ae R hR (frequencyWindowRestriction R F hF),
    frequencyWindow_ae R (hLp.toLp F), hLp.coeFn_toLp] with x he hw hFae
  rw [he, hw]
  by_cases hx : x ∈ Icc (-R) R
  · simp only [zeroExtendFourierWindow, indicator_of_mem hx, hFae]
    simp [ContinuousMap.IccExtend, Set.IccExtend,
      projIcc_of_mem (show -R ≤ R by linarith) hx, frequencyWindowRestriction]
  · simp [zeroExtendFourierWindow, hx]

/-- Uniformly bounded, uniformly Lipschitz Fourier data have compact
closure after an actual finite-frequency cutoff in the full L² space. -/
theorem isCompact_closure_range_frequencyWindow {ι : Type*} {R : ℝ} (hR : 0 < R)
    (F : ι → ℝ → ℂ) (hLp : ∀ i, MemLp (F i) 2 volume) (B L : ℝ≥0)
    (hbound : ∀ i x, ‖F i x‖ ≤ (B : ℝ)) (hLip : ∀ i, LipschitzWith L (F i)) :
    IsCompact (closure (range (fun i => frequencyWindow R ((hLp i).toLp (F i))))) := by
  let G : ι → C(FourierWindow R, ℂ) := fun i =>
    frequencyWindowRestriction R (F i) (hLip i).continuous
  have hK : IsCompact (closure (range G)) := by
    apply isCompact_closure_continuousMap_range_of_uniform_bounds G B L
    · intro i x
      exact hbound i x
    · intro i
      simpa only [mul_one] using (hLip i).comp (LipschitzWith.subtype_val (Icc (-R) R))
  have himage := hK.image (fourierWindowToLp_continuous R hR.le)
  apply himage.of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ himage.isClosed
  rintro u ⟨i, rfl⟩
  refine ⟨G i, subset_closure (mem_range_self i), ?_⟩
  exact fourierWindowToLp_restriction R hR.le (F i) (hLip i).continuous (hLp i)

end Torsion.Spectral

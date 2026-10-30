import Torsion.MarkedFluxFixedKernel
import Torsion.FixedKernelContinuity

/-!
# Differentiating genuine marked flux from a strong H¹ parameter limit

All boundary quotients are identified with one fixed reflection kernel.
The limit is then proved by L² Cauchy--Schwarz on the actual weak gradients.
No convergence of pointwise boundary derivatives is an input.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion
open WeakHarmonicRegularity

/-- The fixed marked-gradient functional has its actual scalar linearity. -/
theorem markedGradientFlux_smul (r : ℝ) (g : Plane → Plane) (c : ℝ) :
    markedGradientFlux r (fun z => c • g z) = c * markedGradientFlux r g := by
  unfold markedGradientFlux
  rw [reflectedGradient_smul]
  have heq : (fun z => c • g z - c • reflectedGradient g z) =
      (fun z => c • (g z - reflectedGradient g z)) := by
    funext z
    rw [smul_sub]
  rw [heq, mollifyGradient_smul]
  simp

/-- Fixed radial smoothing turns strong L² gradient convergence into
convergence of the actual marked-gradient functional, for any parameter filter. -/
theorem markedGradientFlux_tendsto_of_eLpNorm_sub
    {A : Type*} {l : Filter A} {g : A → Plane → Plane} {h : Plane → Plane}
    {r : ℝ} (hr : 0 < r) (hg : ∀ᶠ a in l, MemLp (g a) 2 volume)
    (hh : MemLp h 2 volume)
    (hlim : Tendsto (fun a => eLpNorm (fun z => g a z - h z) 2 volume) l (𝓝 0)) :
    Tendsto (fun a => markedGradientFlux r (g a)) l (𝓝 (markedGradientFlux r h)) := by
  have h := mollifyOddGradient_tendsto_of_eLpNorm_sub_filter_eventually
    hg hh (radialKernel_contDiff r).continuous (radialKernel_hasCompactSupport hr) hlim
    (0 : Plane)
  exact Complex.continuous_im.continuousAt.tendsto.comp h

/-- Any scaled family of genuine harmonic marked fluxes converges when its
actual scaled weak gradients converge strongly in L². Validity is required
only eventually in the parameter filter. -/
theorem scaled_markedFlux_tendsto_of_eLpNorm_gradient
    {A : Type*} {l : Filter A} {u : A → Plane → ℝ} {g : A → Plane → Plane}
    {q c : A → ℝ} {h : Plane → Plane} {r : ℝ}
    (hr : 0 < r) (hh : MemLp h 2 volume)
    (hdata : ∀ᶠ a in l, MemH10 upperHalfPlane (u a) (g a) ∧
      IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 (4 * r)) (u a) (g a) ∧
      ∃ s : ℝ, 0 < s ∧ ContinuousOn (u a) (upperHalfPlane ∩ Metric.ball 0 s) ∧
        HasMarkedFlux (u a) (q a))
    (hlim : Tendsto (fun a =>
      eLpNorm (fun z => c a • g a z - h z) 2 volume) l (𝓝 0)) :
    Tendsto (fun a => c a * q a) l (𝓝 (markedGradientFlux r h)) := by
  have hg : ∀ᶠ a in l, MemLp (fun z => c a • g a z) 2 volume := by
    filter_upwards [hdata] with a ha
    exact ha.1.2.1.const_smul (c a)
  have h := markedGradientFlux_tendsto_of_eLpNorm_sub hr hg hh hlim
  apply h.congr'
  filter_upwards [hdata] with a ha
  obtain ⟨s, hs, hc, hq⟩ := ha.2.2
  rw [markedGradientFlux_smul, hq.eq_fixedGradientKernel ha.1 ha.2.1 hr hs hc]

/-- Finite marked fluxes respect subtraction of their actual representatives. -/
theorem HasMarkedFlux.sub {u v : Plane → ℝ} {q p : ℝ}
    (hq : HasMarkedFlux u q) (hp : HasMarkedFlux v p) :
    HasMarkedFlux (fun z => u z - v z) (q - p) := by
  simpa only [HasMarkedFlux, sub_div] using Filter.Tendsto.sub hq hp

/-- A fixed-patch material H¹ derivative gives an actual marked-flux
parameter derivative. The local harmonic equation is required of the
differences, as supplied by a deformation that is the identity near zero.
There is no boundary-derivative convergence hypothesis. -/
theorem markedFlux_hasDerivWithinAt_of_eLpNorm_gradient_quotient
    {S : Set ℝ} {u : ℝ → Plane → ℝ} {g : ℝ → Plane → Plane}
    {q : ℝ → ℝ} {h : Plane → Plane} {r s₀ : ℝ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hu₀ : MemH10 upperHalfPlane (u 0) (g 0))
    (hc₀ : ContinuousOn (u 0) (upperHalfPlane ∩ Metric.ball 0 s₀))
    (hq₀ : HasMarkedFlux (u 0) (q 0)) (hh : MemLp h 2 volume)
    (hdata : ∀ᶠ t in 𝓝[S \ {0}] 0,
      MemH10 upperHalfPlane (u t) (g t) ∧
      IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 (4 * r))
        (fun z => u t z - u 0 z) (fun z => g t z - g 0 z) ∧
      ∃ s : ℝ, 0 < s ∧ ContinuousOn (u t) (upperHalfPlane ∩ Metric.ball 0 s) ∧
        HasMarkedFlux (u t) (q t))
    (hlim : Tendsto (fun t : ℝ =>
      eLpNorm (fun z => t⁻¹ • (g t z - g 0 z) - h z) 2 volume)
      (𝓝[S \ {0}] 0) (𝓝 0)) :
    HasDerivWithinAt q (markedGradientFlux r h) S 0 := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have hdiff : ∀ᶠ t in 𝓝[S \ {0}] 0,
      MemH10 upperHalfPlane (fun z => u t z - u 0 z) (fun z => g t z - g 0 z) ∧
      IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 (4 * r))
        (fun z => u t z - u 0 z) (fun z => g t z - g 0 z) ∧
      ∃ s : ℝ, 0 < s ∧ ContinuousOn (fun z => u t z - u 0 z)
          (upperHalfPlane ∩ Metric.ball 0 s) ∧
        HasMarkedFlux (fun z => u t z - u 0 z) (q t - q 0) := by
    filter_upwards [hdata] with t ht
    obtain ⟨s, hs, hc, hq⟩ := ht.2.2
    refine ⟨ht.1.sub hu₀, ht.2.1, min s s₀, lt_min hs hs₀, ?_, hq.sub hq₀⟩
    exact (hc.mono (inter_subset_inter_right _
      (Metric.ball_subset_ball (min_le_left _ _)))).sub
      (hc₀.mono (inter_subset_inter_right _
        (Metric.ball_subset_ball (min_le_right _ _))))
  have h := scaled_markedFlux_tendsto_of_eLpNorm_gradient hr hh hdiff hlim
  convert h using 1
  funext t
  simp only [slope_def_field, sub_zero, div_eq_mul_inv, mul_comm]

end Torsion

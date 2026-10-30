module

public import Torsion.MarkedFlux
public import Torsion.DirichletExhaustion
public import Torsion.WeakHarmonicWeyl.ConvolutionEstimates

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Actual marked-flux convergence along increasing domains -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Torsion
open WeakHarmonicRegularity

private theorem halfBall_open (r : ℝ) : IsOpen (upperHalfPlane ∩ Metric.ball (0 : Plane) r) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball

private theorem markedFlux_of_smooth {v : Plane → ℝ} (hv : ContDiff ℝ ∞ v)
    (hv0 : v 0 = 0) : HasMarkedFlux v (gradient v 0).im := by
  have hline : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const Complex.I
  have hdv : HasFDerivAt v (fderiv ℝ v 0) ((0 : ℂ) * Complex.I) := by
    simpa using (hv.differentiable (by simp) 0).hasFDerivAt
  have hd : HasDerivAt (fun t : ℝ => v ((t : ℂ) * Complex.I)) (gradient v 0).im 0 := by
    have heq : fderiv ℝ v 0 Complex.I = (gradient v 0).im := by
      simp only [fderiv_apply_eq_inner_gradient, Complex.inner, Complex.mul_re,
        Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, mul_one, one_mul, zero_sub, sub_zero, neg_neg]
    simpa only [heq, Function.comp_apply] using! hdv.comp_hasDerivAt 0 hline
  exact hasMarkedFlux_of_normal_derivative hv0 hd

/-- For an actual weakly harmonic zero-trace half-ball pair, the inward flux
is exactly a fixed radial average of its odd weak gradient. -/
private theorem harmonic_flux_eq_mollified_odd_gradient
    {u : Plane → ℝ} {g : Plane → Plane} {r s q : ℝ}
    (hu : MemH10 upperHalfPlane u g)
    (hw : IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 (4 * r)) u g)
    (hr : 0 < r) (hs : 0 < s)
    (hc : ContinuousOn u (upperHalfPlane ∩ Metric.ball 0 s)) (hq : HasMarkedFlux u q) :
    q = (mollifyGradient (fun z => g z - reflectedGradient g z) (radialKernel r) 0).im := by
  let w : Plane → ℝ := fun z => u z - reflectedValue u z
  let h : Plane → Plane := fun z => g z - reflectedGradient g z
  have hmem : MemH10 univ w h :=
    (hu.mono (subset_univ _)).sub (hu.reflectedValue.mono (subset_univ _))
  have hweak : IsWeakHarmonicOn (Metric.ball 0 (4 * r)) w h := hw.odd_reflection hu
  obtain ⟨v, hv, hAE, hG⟩ := hweak.exists_smoothRepresentative_on_ball hmem hr Subset.rfl
  have hodd : ∀ z, w (star z) = -w z := by
    intro z
    simp only [w, reflectedValue, star_star]
    ring
  have hv0 := zero_at_origin_of_continuous_ae_odd_on_ball (half_pos hr)
    hv.continuous.continuousOn hAE hodd
  have hflux := markedFlux_of_smooth hv hv0
  have hker := gradient_ae_eq_radial_mollifyGradient_on_ball
    hmem.1 hmem.2.1 hweak hr Subset.rfl
  have hGsmall : gradient v =ᵐ[volume.restrict (Metric.ball 0 (r / 2))]
      mollifyGradient h (radialKernel r) :=
    hG.symm.trans (ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_ball (half_le_self hr.le)) hker)
  have hpointG := Measure.eqOn_open_of_ae_eq hGsmall Metric.isOpen_ball
    (gradient_contDiff hv).continuous.continuousOn
    (mollifyGradient_contDiff hmem.2.1 (radialKernel_contDiff r)
      (radialKernel_hasCompactSupport hr)).continuous.continuousOn
  have hG0 := hpointG (Metric.mem_ball_self (half_pos hr))
  let a : ℝ := min s (r / 2)
  have ha : 0 < a := lt_min hs (half_pos hr)
  have hsmallH : upperHalfPlane ∩ Metric.ball (0 : Plane) a ⊆ upperHalfPlane :=
    inter_subset_left
  have hsmallB : upperHalfPlane ∩ Metric.ball (0 : Plane) a ⊆
      Metric.ball 0 (r / 2) :=
    inter_subset_right.trans (Metric.ball_subset_ball (min_le_right _ _))
  have hsmallS : upperHalfPlane ∩ Metric.ball (0 : Plane) a ⊆
      upperHalfPlane ∩ Metric.ball 0 s :=
    inter_subset_inter_right _ (Metric.ball_subset_ball (min_le_left _ _))
  have hUpper : w =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 a)] u :=
    ae_restrict_of_ae_restrict_of_subset hsmallH hu.odd_reflection_ae_upper
  have hSmall : w =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 a)] v :=
    ae_restrict_of_ae_restrict_of_subset hsmallB hAE
  have hEq : u =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 a)] v :=
    hUpper.symm.trans hSmall
  have hpoint := Measure.eqOn_open_of_ae_eq hEq (halfBall_open a)
    (hc.mono hsmallS) hv.continuous.continuousOn
  have hqv : HasMarkedFlux v q := by
    apply hq.congr'
    filter_upwards [eventually_vertical_mem_halfBall ha] with t ht
    rw [hpoint ht]
  have heq := hqv.unique hflux
  rw [heq, hG0]

private theorem markedFlux_sub {u v : Plane → ℝ} {q p : ℝ}
    (hq : HasMarkedFlux u q) (hp : HasMarkedFlux v p) :
    HasMarkedFlux (fun z => u z - v z) (q - p) := by
  simpa only [HasMarkedFlux, sub_div] using hq.sub hp

/-- Genuine flux differences can be read from a fixed kernel applied to the
odd extension of the actual weak-gradient difference. -/
private theorem torsion_flux_difference_kernel
    {D E : Set Plane} {u v : Plane → ℝ} {g h : Plane → Plane}
    {q p r s t : ℝ}
    (hu : IsWeakTorsion D u g) (hv : IsWeakTorsion E v h)
    (hDH : D ⊆ upperHalfPlane) (hEH : E ⊆ upperHalfPlane)
    (hBD : upperHalfPlane ∩ Metric.ball 0 (4 * r) ⊆ D)
    (hBE : upperHalfPlane ∩ Metric.ball 0 (4 * r) ⊆ E)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hcU : ContinuousOn u (upperHalfPlane ∩ Metric.ball 0 s))
    (hcV : ContinuousOn v (upperHalfPlane ∩ Metric.ball 0 t))
    (hqu : HasMarkedFlux u q) (hpv : HasMarkedFlux v p) :
    q - p = (mollifyGradient
      (fun z => (g z - h z) - reflectedGradient (fun x => g x - h x) z)
      (radialKernel r) 0).im := by
  have hm := (hu.1.mono hDH).sub (hv.1.mono hEH)
  have hw := hu.difference_weakHarmonicOn hv hBD hBE
  have hc : ContinuousOn (fun z => u z - v z)
      (upperHalfPlane ∩ Metric.ball 0 (min s t)) :=
    (hcU.mono (inter_subset_inter_right _
      (Metric.ball_subset_ball (min_le_left _ _)))).sub
    (hcV.mono (inter_subset_inter_right _
      (Metric.ball_subset_ball (min_le_right _ _))))
  exact harmonic_flux_eq_mollified_odd_gradient hm hw hr (lt_min hs ht) hc
    (markedFlux_sub hqu hpv)

/-- Lemma 3.7: the actual finite marked torsion flux converges along every
increasing marked-domain exhaustion with marked bounded union. A flat patch
of the first domain is common to the whole exhaustion; weak H¹ convergence,
odd reflection and the proved fixed-kernel Weyl identity give the limit. -/
theorem torsionFlux_tendsto_of_exhaustion {D : ℕ → Set Plane}
    (hmono : Monotone D) (hmarked : ∀ n, IsMarked (D n))
    (hUnion : IsMarked (⋃ n, D n)) :
    Tendsto (fun n => torsionFlux (D n)) atTop (𝓝 (torsionFlux (⋃ n, D n))) := by
  obtain ⟨u, g, s, hu, hs, hc, hf⟩ := torsionFlux_spec hUnion
  choose un gn sn hun hsn hcn hfn using (fun n => torsionFlux_spec (hmarked n))
  have hlim := hu.tendsto_eLpNorm_gradient_of_exhaustion hmono
    (fun n => (hmarked n).1) hun
  obtain ⟨R, hR, hflat⟩ := (hmarked 0).2.2.2
  let r : ℝ := R / 8
  have hr : 0 < r := by dsimp [r]; positivity
  have hsmall : upperHalfPlane ∩ Metric.ball (0 : Plane) (4 * r) ⊆ D 0 := by
    intro z hz
    have hzR : z ∈ upperHalfPlane ∩ Metric.ball (0 : Plane) R :=
      ⟨hz.1, Metric.ball_subset_ball (by dsimp [r]; linarith) hz.2⟩
    rw [← hflat] at hzR
    exact hzR.1
  have hBD (n : ℕ) : upperHalfPlane ∩ Metric.ball (0 : Plane) (4 * r) ⊆ D n :=
    hsmall.trans (hmono (Nat.zero_le n))
  have hBU : upperHalfPlane ∩ Metric.ball (0 : Plane) (4 * r) ⊆ ⋃ n, D n :=
    hsmall.trans (subset_iUnion D 0)
  let k : ℕ → Plane → Plane := fun n z => gn n z - g z
  let H : ℕ → Plane → Plane := fun n z => k n z - reflectedGradient (k n) z
  have hk (n : ℕ) : MemLp (k n) 2 volume := (hun n).1.2.1.sub hu.1.2.1
  have hH (n : ℕ) : MemLp (H n) 2 volume := (hk n).sub (memLp_reflectedGradient (hk n))
  have hnormRef (n : ℕ) : eLpNorm (reflectedGradient (k n)) 2 volume =
      eLpNorm (k n) 2 volume := by
    calc
      _ = eLpNorm (fun z => k n (star z)) 2 volume := by
        apply eLpNorm_congr_norm_ae
          (memLp_reflectedGradient (hk n)).aestronglyMeasurable
          ((hk n).comp_measurePreserving measurePreserving_conjugation).aestronglyMeasurable
        exact ae_of_all _ fun z => norm_star (k n (star z))
      _ = _ := eLpNorm_comp_conjugation (k n) 2
  have hlimH : Tendsto (fun n => eLpNorm (H n) 2 volume) atTop (𝓝 0) := by
    have hbound (n : ℕ) : eLpNorm (H n) 2 volume ≤
        eLpNorm (k n) 2 volume + eLpNorm (k n) 2 volume := by
      have hb := eLpNorm_sub_le (f := k n) (g := reflectedGradient (k n)) (μ := volume)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      change eLpNorm (k n - reflectedGradient (k n)) 2 volume ≤ _
      simpa only [hnormRef] using hb
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hlim.add hlim) (fun _ => zero_le) hbound
  have hsmooth := mollifyGradient_tendsto_zero_of_eLpNorm hH
    ((radialKernel_contDiff r).continuous.memLp_of_hasCompactSupport
      (radialKernel_hasCompactSupport hr)) hlimH (0 : Plane)
  have him := Complex.continuous_im.continuousAt.tendsto.comp hsmooth
  apply tendsto_sub_nhds_zero_iff.mp
  have heq (n : ℕ) : torsionFlux (D n) - torsionFlux (⋃ n, D n) =
      (mollifyGradient (H n) (radialKernel r) 0).im :=
    torsion_flux_difference_kernel (hun n) hu (hmarked n).2.2.1 hUnion.2.2.1
      (hBD n) hBU hr (hsn n) hs (hcn n) hc (hfn n) hf
  simpa only [Complex.zero_im, heq, Function.comp_apply] using! him

end Torsion

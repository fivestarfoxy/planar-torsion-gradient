import Torsion.WeakReflection.ZeroGradient
import Torsion.SobolevLocalization
import Torsion.WeakHarmonicWeyl.RepresentativeGradient

/-!
# Actual local value representatives from the mollified weak gradient

Once the weak gradient agrees locally with one fixed smooth convolution,
the actual value agrees with its smooth primitive up to an additive constant.
A compact cutoff makes the subtraction an honest global H¹ pair; the proved
zero-gradient constancy lemma then identifies the actual value class.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion
open WeakHarmonicRegularity

/-- Construct a genuine smooth value representative, and identify its
classical gradient with the original actual weak gradient, from a local
fixed-kernel gradient identity. No value-representative or primitive-existence
assumption is needed. -/
theorem MemH10.exists_smoothRepresentative_of_mollified_gradient
    {E : Set Plane} {u κ : Plane → ℝ} {g : Plane → Plane} (hu : MemH10 E u g)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) {c : Plane} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hgrad : g =ᵐ[volume.restrict (Metric.ball c R)] mollifyGradient g κ) :
    ∃ v : Plane → ℝ, ContDiff ℝ ∞ v ∧
      (u =ᵐ[volume.restrict (Metric.ball c ρ)] v) ∧
      (g =ᵐ[volume.restrict (Metric.ball c ρ)] gradient v) := by
  let f : Plane → ℝ := mollify u κ
  have hf : ContDiff ℝ ∞ f := mollify_contDiff hu.1 hκ hc
  have hfgrad (z : Plane) : gradient f z = mollifyGradient g κ z :=
    (mollify_hasGradientAt hu.1 hu.2.1 hu.distributionalGradient hκ hc z).gradient
  obtain ⟨η, hη, hηone⟩ := exists_test_eq_one_near_compact isOpen_univ
    (isCompact_closedBall c R) (subset_univ _)
  let p : Plane → ℝ := fun z => η z * f z
  have hp : IsTest univ p := hη.mul_left hf
  have hpNear {z : Plane} (hz : z ∈ Metric.ball c R) : p =ᶠ[𝓝 z] f := by
    have heq := hηone.filter_mono
      (nhds_le_nhdsSet (Metric.ball_subset_closedBall hz))
    filter_upwards [heq] with x hx
    simp only [p, hx, one_mul]
  have hpEq (z : Plane) (hz : z ∈ Metric.ball c R) : p z = f z :=
    (hpNear hz).self_of_nhds
  have hpG (z : Plane) (hz : z ∈ Metric.ball c R) : gradient p z = gradient f z := by
    unfold gradient
    rw [(hpNear hz).fderiv_eq]
  have hdiff := (hu.mono (subset_univ _)).sub hp.memH10
  have hzero : (fun z => g z - gradient p z) =ᵐ[volume.restrict (Metric.ball c R)] 0 := by
    filter_upwards [hgrad, ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzB
    change g z - gradient p z = 0
    rw [hpG z hzB, hfgrad z, hz, sub_self]
  obtain ⟨k, hk⟩ := hdiff.distributionalGradient.ae_constant_on_smaller_ball
    hdiff.1 hdiff.2.1 hρ hρR hzero
  let v : Plane → ℝ := fun z => f z + k
  have hv : ContDiff ℝ ∞ v := hf.add contDiff_const
  have hvG (z : Plane) : gradient v z = gradient f z := by
    unfold gradient
    rw [fderiv_add_const]
  refine ⟨v, hv, ?_, ?_⟩
  · filter_upwards [hk, ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzB
    have hzR := Metric.ball_subset_ball hρR.le hzB
    have hz' : u z - f z = k := by simpa only [hpEq z hzR] using hz
    dsimp [v]
    linarith
  · have hgradSmall := ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_ball hρR.le : Metric.ball c ρ ⊆ Metric.ball c R) hgrad
    filter_upwards [hgradSmall] with z hz
    rw [hvG, hfgrad]
    exact hz

/-- Local Weyl regularity for the actual H¹ graph on any full ball compactly
inside the weakly harmonic region. The fixed smooth representative and its
gradient are constructed, with no regularity input. -/
theorem IsWeakHarmonicOn.exists_smoothRepresentative_on_ball
    {U E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} {c : Plane} {r : ℝ}
    (hw : IsWeakHarmonicOn U u g) (hu : MemH10 E u g) (hr : 0 < r)
    (hball : Metric.ball c (4 * r) ⊆ U) :
    ∃ v : Plane → ℝ, ContDiff ℝ ∞ v ∧
      (u =ᵐ[volume.restrict (Metric.ball c (r / 2))] v) ∧
      (g =ᵐ[volume.restrict (Metric.ball c (r / 2))] gradient v) := by
  exact hu.exists_smoothRepresentative_of_mollified_gradient
    (radialKernel_contDiff r) (radialKernel_hasCompactSupport hr)
    (half_pos hr) (half_lt_self hr)
    (gradient_ae_eq_radial_mollifyGradient_on_ball hu.1 hu.2.1 hw hr hball)

private theorem translated_radialKernel_tsupport_subset {r : ℝ} (hr : 0 < r) (x : Plane) :
    tsupport (fun t => radialKernel r (x - t)) ⊆ Metric.closedBall x r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro t ht
  have htκ : x - t ∈ Function.support (radialKernel r) := ht
  rw [radialKernel_support hr] at htκ
  apply Metric.mem_closedBall.mpr
  have hdist : dist t x < r := by
    simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, norm_sub_rev, sub_zero] using htκ
  exact hdist.le

/-- The constructed local Weyl representative is classically harmonic,
with the original actual weak gradient as its a.e. classical gradient. -/
theorem IsWeakHarmonicOn.exists_smooth_harmonicRepresentative_on_ball
    {U E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} {c : Plane} {r : ℝ}
    (hw : IsWeakHarmonicOn U u g) (hu : MemH10 E u g) (hr : 0 < r)
    (hball : Metric.ball c (4 * r) ⊆ U) :
    ∃ v : Plane → ℝ, ContDiff ℝ ∞ v ∧
      (u =ᵐ[volume.restrict (Metric.ball c (r / 2))] v) ∧
      (g =ᵐ[volume.restrict (Metric.ball c (r / 2))] gradient v) ∧
      (∀ z ∈ Metric.ball c (r / 2), planarLaplacian v z = 0) := by
  obtain ⟨v, hv, huAE, hgAE⟩ := hw.exists_smoothRepresentative_on_ball hu hr hball
  let f : Plane → ℝ := mollify u (radialKernel r)
  have hf : ContDiff ℝ ∞ f :=
    mollify_contDiff hu.1 (radialKernel_contDiff r) (radialKernel_hasCompactSupport hr)
  have hfg := gradient_ae_eq_gradient_radial_mollify_on_ball hu.1 hu.2.1 hw hr hball
  have hgradAE : gradient v =ᵐ[volume.restrict (Metric.ball c (r / 2))] gradient f :=
    hgAE.symm.trans (ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_ball (half_lt_self hr).le) hfg)
  have hvG : Continuous (gradient v) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp
      (hv.continuous_fderiv (by simp))
  have hfG : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp
      (hf.continuous_fderiv (by simp))
  have hgradEq := Measure.eqOn_open_of_ae_eq hgradAE Metric.isOpen_ball
    hvG.continuousOn hfG.continuousOn
  refine ⟨v, hv, huAE, hgAE, ?_⟩
  intro z hz
  have hgradNear : gradient v =ᶠ[𝓝 z] gradient f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with x hx
    exact hgradEq hx
  have hLap : planarLaplacian v z = planarLaplacian f z := by
    unfold planarLaplacian planarDivergence
    rw [hgradNear.fderiv_eq]
  rw [hLap]
  apply mollify_laplacian_eq_zero hu.1 hu.2.1 hw
    (radialKernel_contDiff r) (radialKernel_hasCompactSupport hr)
  intro t ht
  have htz := translated_radialKernel_tsupport_subset hr z ht
  have hdist := dist_triangle t z c
  have htzr := Metric.mem_closedBall.mp htz
  have hzcr := Metric.mem_ball.mp hz
  apply hball
  apply Metric.mem_ball.mpr
  linarith

end Torsion

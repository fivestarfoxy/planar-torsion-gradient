module

public import Torsion.HarmonicNormalTaylor
public import Torsion.SlabTorsionBarrier
public import Torsion.MarkedFlux

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Uniform marked torsion Taylor estimates from the actual slab barrier

A local linear torsion bound controls the odd harmonic correction on a full
fixed ball. Caccioppoli and the fixed convolution then give a domain-uniform
normal quotient estimate for a constructed genuine torsion representative.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- An odd actual function bounded on the upper half-ball has the same
absolute bound almost everywhere on the full ball. The real diameter is
handled by oddness itself, without sampling an a.e. assertion there. -/
theorem ae_abs_le_on_ball_of_odd_upper_bound
    {w : Plane → ℝ} {R M : ℝ} (hM : 0 ≤ M)
    (hodd : ∀ z, w (star z) = -w z)
    (hupper : ∀ᵐ z ∂volume.restrict (upperHalfPlane ∩ Metric.ball (0 : Plane) R),
      |w z| ≤ M) :
    ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Plane) R), |w z| ≤ M := by
  have hmeas : MeasurableSet (upperHalfPlane ∩ Metric.ball (0 : Plane) R) :=
    ((isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball).measurableSet
  have hglob := (ae_restrict_iff' hmeas).mp hupper
  have href := measurePreserving_conjugation.quasiMeasurePreserving.ae hglob
  apply (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr
  filter_upwards [hglob, href] with z hz hzr
  intro hzB
  by_cases hzi : 0 < z.im
  · exact hz ⟨hzi, hzB⟩
  · by_cases hzn : z.im < 0
    · have hstar : star z ∈ upperHalfPlane ∩ Metric.ball (0 : Plane) R := by
        refine ⟨?_, ?_⟩
        · simpa only [upperHalfPlane, mem_setOf_eq, Complex.star_def, Complex.conj_im] using neg_pos.mpr hzn
        · simpa only [Metric.mem_ball, dist_zero_right, norm_star] using hzB
      simpa only [hodd, abs_neg] using hzr hstar
    · have him : z.im = 0 := le_antisymm (le_of_not_gt hzi) (le_of_not_gt hzn)
      have hstar : star z = z := Complex.conj_eq_iff_im.mpr him
      have hwz := hodd z
      rw [hstar] at hwz
      have hwzero : w z = 0 := by linarith
      simpa only [hwzero, abs_zero] using hM

/-- For one fixed marked half-ball, a single geometric constant controls
normal quotients for every actual weak torsion solution having a linear
upper barrier. A smooth genuine representative is constructed on the
entire smaller half-ball, rather than an unspecified shrinking patch. -/
theorem exists_uniform_marked_torsion_normal_quotient_constant {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} {B : ℝ},
      IsMarked D → IsWeakTorsion D u g → 0 ≤ B →
      upperHalfPlane ∩ Metric.ball (0 : Plane) (4*r) ⊆ D →
      (∀ᵐ z ∂volume.restrict D, u z ≤ B*z.im) →
      ∃ U : Plane → ℝ, ContDiff ℝ ∞ U ∧ U 0 = 0 ∧
        (u =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 (r/2))] U) ∧
        HasMarkedFlux U (torsionFlux D) ∧
        ∀ h : ℝ, 0 < h → h < r/2 →
          |U ((h : Plane)*Complex.I)/h - torsionFlux D| ≤
            (C*(4*r*B + 8*r^2) + 1/2)*h := by
  obtain ⟨C, hC, hTaylor⟩ := exists_uniform_harmonic_normal_quotient_constant hr
  refine ⟨C, hC, ?_⟩
  intro D u g B hD hu hB hhalf hbound
  obtain ⟨w, k, hm, hw, hwAE, hodd⟩ :=
    hu.exists_odd_harmonic_extension hD.2.2.1 (4*r) hhalf
  let M : ℝ := 4*r*B + 8*r^2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hupper : ∀ᵐ z ∂volume.restrict (upperHalfPlane ∩ Metric.ball 0 (4*r)),
      |w z| ≤ M := by
    have hnonneg : ∀ᵐ z ∂volume.restrict (upperHalfPlane ∩ Metric.ball (0 : Plane) (4*r)),
        0 ≤ u z := ae_restrict_of_ae (hu.nonneg_ae hD.2.1)
    have hb := ae_restrict_of_ae_restrict_of_subset hhalf hbound
    filter_upwards [hwAE, hnonneg, hb, ae_restrict_mem
      (((isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball).measurableSet)]
      with z hzw hzu hzb hz
    rw [hzw, abs_of_nonneg (add_nonneg hzu (by unfold quadraticIm; positivity))]
    have hzi : 0 < z.im := hz.1
    have hzr : z.im < 4*r := (Complex.im_le_norm z).trans_lt
      (by simpa only [Metric.mem_ball, dist_zero_right] using hz.2)
    have hBu : u z ≤ 4*r*B := hzb.trans (by nlinarith)
    unfold quadraticIm M
    nlinarith
  have hfull := ae_abs_le_on_ball_of_odd_upper_bound hM hodd hupper
  obtain ⟨v, hv, hAE, hG, hvTaylor⟩ := hTaylor hm hw hM hfull
  have hv0 := zero_at_origin_of_continuous_ae_odd_on_ball (half_pos hr)
    hv.continuous.continuousOn hAE hodd
  have hsmall : upperHalfPlane ∩ Metric.ball (0 : Plane) (r/2) ⊆
      upperHalfPlane ∩ Metric.ball 0 (4*r) := by
    apply inter_subset_inter_right
    apply Metric.ball_subset_ball
    linarith
  have hflux := HasTorsionFlux.of_odd_smoothRepresentative hu (half_pos hr) hv
    (ae_restrict_of_ae_restrict_of_subset hsmall hwAE) hAE hodd
  have hq : (gradient v 0).im = torsionFlux D := hflux.eq_torsionFlux hD
  let U : Plane → ℝ := fun z => v z - quadraticIm z
  have hU : ContDiff ℝ ∞ U := hv.sub quadraticIm_contDiff
  have hU0 : U 0 = 0 := by simp [U, hv0, quadraticIm]
  have hrep : u =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 (r/2))] U := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsmall hwAE,
      ae_restrict_of_ae_restrict_of_subset inter_subset_right hAE] with z hwu hwv
    dsimp [U]
    linarith
  have hgrad : gradient U 0 = gradient v 0 := by
    unfold gradient
    change (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ (v - quadraticIm) 0) = _
    rw [fderiv_sub (hv.differentiable (by simp) 0)
      (quadraticIm_contDiff.differentiable (by simp) 0), map_sub]
    change gradient v 0 - gradient quadraticIm 0 = gradient v 0
    rw [gradient_quadraticIm]
    simp
  have hnormal : HasMarkedFlux U (torsionFlux D) := by
    apply hasMarkedFlux_of_normal_derivative hU0
    have hdiff : Differentiable ℝ (fun t : ℝ => U ((t : Plane)*Complex.I)) :=
      (hU.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)).differentiable (by simp)
    convert (hdiff 0).hasDerivAt using 1
    rw [normalLine_deriv hU]
    simpa only [Complex.ofReal_zero, zero_mul, hgrad] using hq.symm
  refine ⟨U, hU, hU0, hrep, hnormal, ?_⟩
  intro h hh hhR
  have hvbound := hvTaylor h hh hhR
  rw [hv0, sub_zero, hq] at hvbound
  have heq : U ((h : Plane)*Complex.I)/h - torsionFlux D =
      (v ((h : Plane)*Complex.I)/h - torsionFlux D) - h/2 := by
    simp only [U, quadraticIm, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero]
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |v ((h : Plane)*Complex.I)/h - torsionFlux D| + |h/2| := abs_sub _ _
    _ ≤ C*M*h + h/2 := by rw [abs_of_pos (half_pos hh)]; exact add_le_add hvbound le_rfl
    _ = (C*(4*r*B + 8*r^2) + 1/2)*h := by dsimp [M]; ring

/-- A containing horizontal slab discharges the linear barrier premise of
the actual fixed-half-ball torsion estimate. -/
theorem exists_uniform_slab_marked_torsion_normal_quotient_constant {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} {b : ℝ},
      IsMarked D → IsWeakTorsion D u g → 0 ≤ b →
      upperHalfPlane ∩ Metric.ball (0 : Plane) (4*r) ⊆ D →
      (∀ z ∈ D, z.im < b) →
      ∃ U : Plane → ℝ, ContDiff ℝ ∞ U ∧ U 0 = 0 ∧
        (u =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 (r/2))] U) ∧
        HasMarkedFlux U (torsionFlux D) ∧
        ∀ h : ℝ, 0 < h → h < r/2 →
          |U ((h : Plane)*Complex.I)/h - torsionFlux D| ≤
            (C*(2*r*b + 8*r^2) + 1/2)*h := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_marked_torsion_normal_quotient_constant hr
  refine ⟨C, hC, ?_⟩
  intro D u g b hD hu hb hhalf hheight
  have hslab : ∀ z ∈ D, 0 < z.im ∧ z.im < b := fun z hz => ⟨hD.2.2.1 hz, hheight z hz⟩
  have hlinear := hu.le_slab_lower_linear hD.1 hD.2.1 hslab
  simp only [sub_zero] at hlinear
  obtain ⟨U, hU, hU0, hrep, hnormal, hTaylor⟩ :=
    hbound hD hu (show 0 ≤ b/2 by positivity) hhalf hlinear
  refine ⟨U, hU, hU0, hrep, hnormal, ?_⟩
  intro h hh hhR
  convert hTaylor h hh hhR using 1
  ring

/-- The same uniform estimate holds for every actual continuous interior
representative. In particular it applies to the constructed smooth global
interior representative of the original weak torsion problem. -/
theorem exists_uniform_slab_marked_torsion_normal_quotient_constant_on_representative
    {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {D : Set Plane} {u W : Plane → ℝ} {g : Plane → Plane} {b : ℝ},
      IsMarked D → IsWeakTorsion D u g → 0 ≤ b →
      upperHalfPlane ∩ Metric.ball (0 : Plane) (4*r) ⊆ D →
      (∀ z ∈ D, z.im < b) → ContinuousOn W D →
      (u =ᵐ[volume.restrict D] W) →
      ∀ h : ℝ, 0 < h → h < r/2 →
        |W ((h : Plane)*Complex.I)/h - torsionFlux D| ≤
          (C*(2*r*b + 8*r^2) + 1/2)*h := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_slab_marked_torsion_normal_quotient_constant hr
  refine ⟨C, hC, ?_⟩
  intro D u W g b hD hu hb hhalf hheight hW hrep h hh hhR
  obtain ⟨U, hU, hU0, hUrep, hnormal, hTaylor⟩ := hbound hD hu hb hhalf hheight
  have hKD : upperHalfPlane ∩ Metric.ball (0 : Plane) (r/2) ⊆ D := by
    apply Subset.trans _ hhalf
    apply inter_subset_inter_right
    apply Metric.ball_subset_ball
    linarith
  have hEq : U =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 (r/2))] W :=
    hUrep.symm.trans (ae_restrict_of_ae_restrict_of_subset hKD hrep)
  have hpoint := Measure.eqOn_open_of_ae_eq hEq
    ((isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball)
    hU.continuous.continuousOn (hW.mono hKD)
  have hhK : (h : Plane)*Complex.I ∈ upperHalfPlane ∩ Metric.ball (0 : Plane) (r/2) := by
    refine ⟨?_, ?_⟩
    · simpa only [upperHalfPlane, mem_setOf_eq, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero] using hh
    · simpa only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hh] using hhR
  rw [← hpoint hhK]
  exact hTaylor h hh hhR

/-- The quotient estimate is exactly a quadratic normal Taylor remainder. -/
theorem abs_normal_remainder_le_sq_of_quotient_bound
    {a Q L h : ℝ} (hh : 0 < h) (hb : |a/h-Q| ≤ L*h) :
    |a-Q*h| ≤ L*h^2 := by
  have heq : a-Q*h = (a/h-Q)*h := by field_simp
  rw [heq, abs_mul, abs_of_pos hh]
  calc
    _ ≤ (L*h)*h := mul_le_mul_of_nonneg_right hb hh.le
    _ = L*h^2 := by ring

end Torsion

module

public import Torsion.Definitions
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic

@[expose] public section

/-!
# Actual radial domains

Geometric admissibility and polar-coordinate area for the domain in (3.4).
The domain is the set defined in `Torsion.Definitions`, not an abstract label.
-/

noncomputable section
namespace Torsion.RadialGeometry

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The open parameter region in radius-angle coordinates. -/
def parameterSet (R : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Ioo 0 Real.pi ∧ p.1 ∈ Ioo 0 (R p.2)}

private theorem parameterSet_subset_target (R : ℝ → ℝ) :
    parameterSet R ⊆ Complex.polarCoord.target := by
  intro p hp
  change 0 < p.1 ∧ -Real.pi < p.2 ∧ p.2 < Real.pi
  exact ⟨hp.2.1, (neg_lt_zero.mpr Real.pi_pos).trans hp.1.1, hp.1.2⟩

private theorem parameterSet_open {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc 0 Real.pi)) : IsOpen (parameterSet R) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hr : ContinuousAt (fun q : ℝ × ℝ => R q.2) p :=
    (hR.continuousAt (Icc_mem_nhds hp.1.1 hp.1.2)).comp continuous_snd.continuousAt
  have hangle : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.2 ∈ Ioo 0 Real.pi :=
    ((isOpen_Ioo.preimage continuous_snd).mem_nhds hp.1)
  have hpos := continuous_const.continuousAt.eventually_lt continuous_fst.continuousAt hp.2.1
  have hlt := continuous_fst.continuousAt.eventually_lt hr hp.2.2
  filter_upwards [hangle, hpos, hlt] with q hq hqp hql
  exact ⟨hq, hqp, hql⟩

theorem radialDomain_eq_polar_image (R : ℝ → ℝ) :
    radialDomain R = Complex.polarCoord.symm '' parameterSet R := by
  ext z
  constructor
  · rintro ⟨θ, r, hθ, hθπ, hr, hrR, rfl⟩
    refine ⟨(r, θ), ⟨⟨hθ, hθπ⟩, ⟨hr, hrR⟩⟩, ?_⟩
    simp [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  · rintro ⟨⟨r, θ⟩, hp, rfl⟩
    refine ⟨θ, r, hp.1.1, hp.1.2, hp.2.1, hp.2.2, ?_⟩
    simp [Complex.polarCoord_symm_apply, Complex.exp_mul_I]

/-- Positive continuous profiles produce open domains even when their radial
boundary is neither Lipschitz nor convex. -/
theorem radialDomain_isOpen {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc 0 Real.pi)) : IsOpen (radialDomain R) := by
  rw [radialDomain_eq_polar_image]
  exact Complex.polarCoord.isOpen_image_symm_of_subset_target
    (parameterSet_open hR) (parameterSet_subset_target R)

private theorem arg_mem_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    z.arg ∈ Ioo 0 Real.pi := by
  constructor
  · refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) ?_
    intro h
    have him := (Complex.arg_eq_zero_iff.mp h.symm).2
    linarith
  · exact Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')

/-- Membership expressed in physical complex coordinates. -/
theorem mem_radialDomain_iff (R : ℝ → ℝ) (z : ℂ) :
    z ∈ radialDomain R ↔ 0 < z.im ∧ ‖z‖ < R z.arg := by
  constructor
  · rintro ⟨θ, r, hθ, hθπ, hr, hrR, rfl⟩
    have ha : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).arg = θ := by
      rw [Complex.exp_mul_I]
      exact Complex.arg_mul_cos_add_sin_mul_I hr
        ⟨(neg_lt_zero.mpr Real.pi_pos).trans hθ, hθπ.le⟩
    have hn : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
      simp [norm_mul, Complex.norm_exp_ofReal_mul_I, abs_of_pos hr]
    constructor
    · simpa [Complex.exp_mul_I, Complex.mul_im, Complex.sin_ofReal_re] using
        mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ hθπ)
    · simpa only [ha, hn] using hrR
  · rintro ⟨hz, hRz⟩
    have harg := arg_mem_of_im_pos hz
    refine ⟨z.arg, ‖z‖, harg.1, harg.2, ?_, hRz, ?_⟩
    · apply norm_pos_iff.mpr
      intro hzero
      simp [hzero] at hz
    · exact (Complex.norm_mul_exp_arg_mul_I z).symm

theorem radialDomain_subset_upperHalfPlane (R : ℝ → ℝ) :
    radialDomain R ⊆ upperHalfPlane := by
  intro z hz
  exact ((mem_radialDomain_iff R z).mp hz).1

/-- Compactness of the closed angular interval bounds the physical domain. -/
theorem radialDomain_bounded {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc 0 Real.pi)) : Bornology.IsBounded (radialDomain R) := by
  obtain ⟨θ, hθ, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) Real.pi).Nonempty from ⟨0, le_rfl, Real.pi_pos.le⟩) hR
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R θ, ?_⟩
  intro z hz
  have hz' := (mem_radialDomain_iff R z).mp hz
  have harg := arg_mem_of_im_pos hz'.1
  exact hz'.2.le.trans (hmax ⟨harg.1.le, harg.2.le⟩)

/-- A positive continuous profile has a common upper-half-ball at the marked
origin. Endpoint values are included in the positivity assumption. -/
theorem radialDomain_isMarked {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc 0 Real.pi))
    (hpos : ∀ θ ∈ Icc 0 Real.pi, 0 < R θ) : IsMarked (radialDomain R) := by
  refine ⟨radialDomain_isOpen hR, radialDomain_bounded hR,
    radialDomain_subset_upperHalfPlane R, ?_⟩
  obtain ⟨θ, hθ, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) Real.pi).Nonempty from ⟨0, le_rfl, Real.pi_pos.le⟩) hR
  refine ⟨R θ, hpos θ hθ, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hb⟩
    exact ⟨radialDomain_subset_upperHalfPlane R hz, hb⟩
  · rintro ⟨hz, hb⟩
    refine ⟨(mem_radialDomain_iff R z).mpr ⟨hz, ?_⟩, hb⟩
    have harg := arg_mem_of_im_pos hz
    have hnorm : ‖z‖ < R θ := by simpa [Metric.mem_ball, dist_zero_right] using hb
    exact hnorm.trans_le (hmin ⟨harg.1.le, harg.2.le⟩)



private theorem mem_polar_symm_iff (R : ℝ → ℝ) {p : ℝ × ℝ}
    (hp : p ∈ Complex.polarCoord.target) :
    Complex.polarCoord.symm p ∈ radialDomain R ↔ p ∈ parameterSet R := by
  rw [radialDomain_eq_polar_image]
  constructor
  · rintro ⟨q, hq, heq⟩
    have hqp := Complex.polarCoord.symm.injOn (parameterSet_subset_target R hq) hp heq
    simpa only [hqp] using hq
  · intro h
    exact ⟨p, h, rfl⟩

private theorem polar_measure (R : ℝ → ℝ) (hR : ContinuousOn R (Icc 0 Real.pi)) :
    volume (radialDomain R) = ∫⁻ p in parameterSet R, ENNReal.ofReal p.1 := by
  have hD := (radialDomain_isOpen hR).measurableSet
  have hS := (parameterSet_open hR).measurableSet
  have hT := polarCoord.open_target.measurableSet
  have hp := Complex.lintegral_comp_polarCoord_symm
    ((radialDomain R).indicator (fun _ : ℂ => (1 : ℝ≥0∞)))
  simp only [lintegral_indicator hD, setLIntegral_const, one_mul, smul_eq_mul] at hp
  rw [← hp]
  rw [← lintegral_indicator hT, ← lintegral_indicator hS]
  apply lintegral_congr
  intro p
  by_cases ht : p ∈ polarCoord.target
  · rw [Set.indicator_of_mem ht]
    by_cases hd : Complex.polarCoord.symm p ∈ radialDomain R
    · have hs := (mem_polar_symm_iff R ht).mp hd
      rw [Set.indicator_of_mem hd, Set.indicator_of_mem hs, mul_one]
    · have hs : p ∉ parameterSet R := fun hs => hd ((mem_polar_symm_iff R ht).mpr hs)
      rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem hs, mul_zero]
  · have hs : p ∉ parameterSet R := fun hs => ht (parameterSet_subset_target R hs)
    rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hs]

private theorem polar_integral_iterated {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc 0 Real.pi)) :
    (∫⁻ p in parameterSet R, ENNReal.ofReal p.1) =
      ∫⁻ θ in Ioo 0 Real.pi, ∫⁻ r in Ioo 0 (R θ), ENNReal.ofReal r := by
  have hS := (parameterSet_open hR).measurableSet
  rw [← lintegral_indicator hS]
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ ((measurable_fst.ennreal_ofReal).indicator hS).aemeasurable]
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro θ
  by_cases hθ : θ ∈ Ioo 0 Real.pi
  · rw [Set.indicator_of_mem hθ, ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro r
    by_cases hr : r ∈ Ioo 0 (R θ)
    · have hp : (r, θ) ∈ parameterSet R := ⟨hθ, hr⟩
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hr]
    · have hp : (r, θ) ∉ parameterSet R := fun hp => hr hp.2
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hr]
  · rw [Set.indicator_of_notMem hθ]
    have hz : ∀ r : ℝ, (r, θ) ∉ parameterSet R := fun r hp => hθ hp.1
    simp only [Set.indicator_of_notMem (hz _), lintegral_zero]

private theorem lintegral_radius {b : ℝ} (hb : 0 ≤ b) :
    (∫⁻ r in Ioo 0 b, ENNReal.ofReal r) = ENNReal.ofReal (b ^ 2 / 2) := by
  have hi : IntegrableOn (fun r : ℝ => r) (Ioo 0 b) :=
    continuous_id.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo 0 b)] (fun r : ℝ => r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hr.1.le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
  congr 1
  rw [← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hb, integral_id]
  norm_num

/-- Equation (3.5) with actual complex-plane Lebesgue measure, obtained from
the polar-coordinate Jacobian and Tonelli's theorem. -/
theorem volume_radialDomain {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc 0 Real.pi))
    (hpos : ∀ θ ∈ Icc 0 Real.pi, 0 < R θ) :
    volume (radialDomain R) = ENNReal.ofReal (radialArea R) := by
  rw [polar_measure R hR, polar_integral_iterated hR]
  have hi : IntegrableOn (fun θ => (R θ) ^ 2 / 2) (Ioo 0 Real.pi) :=
    ((hR.pow 2).integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self |>.div_const 2
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo 0 Real.pi)] (fun θ => (R θ) ^ 2 / 2) := by
    filter_upwards with θ
    positivity
  calc
    _ = ∫⁻ θ in Ioo 0 Real.pi, ENNReal.ofReal ((R θ) ^ 2 / 2) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro θ hθ
      exact lintegral_radius (hpos θ ⟨hθ.1.le, hθ.2.le⟩).le
    _ = ENNReal.ofReal (∫ θ in Ioo 0 Real.pi, (R θ) ^ 2 / 2) :=
      (ofReal_integral_eq_lintegral_ofReal hi hnn).symm
    _ = ENNReal.ofReal (radialArea R) := by
      unfold radialArea
      rw [integral_div]
      congr 1
      ring

/-- The profile area is the real Euclidean area of the actual radial domain. -/
theorem area_radialDomain {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc 0 Real.pi))
    (hpos : ∀ θ ∈ Icc 0 Real.pi, 0 < R θ) :
    (volume (radialDomain R)).toReal = radialArea R := by
  rw [volume_radialDomain hR hpos, ENNReal.toReal_ofReal]
  unfold radialArea
  exact mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioo fun _ _ => sq_nonneg _)

end Torsion.RadialGeometry

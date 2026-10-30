module

public import Torsion.WeakHarmonicWeyl

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Uniform local energy from a local value bound

The cutoff in Caccioppoli's estimate is fixed by the geometric region. Only
the values on that region enter the estimate; arbitrary global extensions
or correction cutoffs do not enter its constant.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Torsion

/-- The Caccioppoli cutoff energy is controlled by a bound on the actual
harmonic region, without using a global value norm. -/
theorem IsWeakHarmonicOn.caccioppoli_energy_of_local_value_bound
    {U E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hw : IsWeakHarmonicOn U u g) (hu : MemH10 E u g)
    (hU : MeasurableSet U) {η : Plane → ℝ} (hη : IsTest U η)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂volume.restrict U, |u x| ≤ M) :
    (∫ x, ‖η x • g x‖ ^ 2) ≤ 4 * M ^ 2 * ∫ x, ‖gradient η x‖ ^ 2 := by
  have hB : MemLp (fun x => u x • gradient η x) 2 volume :=
    (hη.memLp_gradient (p := ∞)).smul hu.1
  have hηI : Integrable (fun x => ‖gradient η x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (hη.memLp_gradient (p := 2)).1).mp
      (hη.memLp_gradient (p := 2))
  have hUI : Integrable (fun x => ‖u x • gradient η x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hB.1).mp hB
  have hb : ∀ᵐ x ∂volume, x ∈ U → |u x| ≤ M :=
    (ae_restrict_iff' hU).mp hbound
  have hineq : (∫ x, ‖u x • gradient η x‖ ^ 2) ≤
      ∫ x, M ^ 2 * ‖gradient η x‖ ^ 2 := by
    apply integral_mono_ae hUI (hηI.const_mul (M ^ 2))
    filter_upwards [hb] with x hx
    by_cases hs : x ∈ tsupport η
    · rw [norm_smul, mul_pow, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) (hx (hη.2.2 hs)) 2) (sq_nonneg _)
    · rw [gradient_eq_zero_of_not_mem_tsupport hs]
      simp
  rw [integral_const_mul] at hineq
  have hbase := hw.caccioppoli_energy hu hη
  nlinarith

/-- A local essential bound gives a fixed geometric bound for the gradient
energy on every compactly contained measurable set. -/
theorem IsWeakHarmonicOn.local_energy_le_of_local_value_bound
    {U E K : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hw : IsWeakHarmonicOn U u g) (hu : MemH10 E u g)
    (hU : MeasurableSet U) {η : Plane → ℝ} (hη : IsTest U η)
    (hK : MeasurableSet K) (hηK : ∀ x ∈ K, η x = 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂volume.restrict U, |u x| ≤ M) :
    (∫ x in K, ‖g x‖ ^ 2) ≤ 4 * M ^ 2 * ∫ x, ‖gradient η x‖ ^ 2 := by
  have hA : MemLp (fun x => η x • g x) 2 volume :=
    hu.2.1.smul (hη.memLp_value (p := ∞))
  calc
    (∫ x in K, ‖g x‖ ^ 2) = ∫ x in K, ‖η x • g x‖ ^ 2 := by
      apply setIntegral_congr_fun hK
      intro x hx
      dsimp only
      rw [hηK x hx, one_smul]
    _ ≤ ∫ x, ‖η x • g x‖ ^ 2 :=
      setIntegral_le_integral ((memLp_two_iff_integrable_sq_norm hA.1).mp hA)
        (ae_of_all _ fun x => sq_nonneg _)
    _ ≤ _ := hw.caccioppoli_energy_of_local_value_bound hu hU hη hM hbound

/-- A single positive constant depending only on `U` and `K` controls every
actual weakly harmonic Sobolev pair with a given local essential bound. -/
theorem exists_local_harmonic_energy_constant_of_local_bound {U K : Set Plane}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ {E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} {M : ℝ},
      MemH10 E u g → IsWeakHarmonicOn U u g → 0 ≤ M →
      (∀ᵐ x ∂volume.restrict U, |u x| ≤ M) →
      (∫ x in K, ‖g x‖ ^ 2) ≤ C * M ^ 2 := by
  obtain ⟨η, hη, hone⟩ := exists_test_eq_one_near_compact hU hK hKU
  let A : ℝ := ∫ x, ‖gradient η x‖ ^ 2
  have hA : 0 ≤ A := integral_nonneg (fun x => sq_nonneg _)
  refine ⟨4 * A + 1, by positivity, ?_⟩
  intro E u g M hu hw hM hb
  have hηK : ∀ x ∈ K, η x = 1 := fun x hx =>
    (hone.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds
  have hbase := hw.local_energy_le_of_local_value_bound hu hU.measurableSet hη
    hK.measurableSet hηK hM hb
  change (∫ x in K, ‖g x‖ ^ 2) ≤ (4 * A + 1) * M ^ 2
  change (∫ x in K, ‖g x‖ ^ 2) ≤ 4 * M ^ 2 * A at hbase
  nlinarith [sq_nonneg M]

/-- Fixed concentric balls have a uniform weak-gradient energy constant,
independent of the domain carrying the original global Sobolev pair. -/
theorem exists_uniform_ball_harmonic_energy_constant {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} {M : ℝ},
      MemH10 E u g → IsWeakHarmonicOn (Metric.ball (0 : Plane) (4*r)) u g → 0 ≤ M →
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Plane) (4*r)), |u x| ≤ M) →
      (∫ x in Metric.closedBall (0 : Plane) (2*r), ‖g x‖ ^ 2) ≤ C * M ^ 2 := by
  apply exists_local_harmonic_energy_constant_of_local_bound Metric.isOpen_ball
    (isCompact_closedBall (0 : Plane) (2*r))
  intro x hx
  change dist x (0 : Plane) ≤ 2*r at hx
  change dist x (0 : Plane) < 4*r
  linarith

/-- The local clipped L² norm has a uniform real bound. This is the form
used in fixed-kernel derivative estimates for the actual smooth representative. -/
theorem exists_uniform_ball_harmonic_L2_constant {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane} {M : ℝ},
      MemH10 E u g → IsWeakHarmonicOn (Metric.ball (0 : Plane) (4*r)) u g → 0 ≤ M →
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Plane) (4*r)), |u x| ≤ M) →
      (eLpNorm ((Metric.ball (0 : Plane) (2*r)).indicator g) 2 volume).toReal ≤ C * M := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_ball_harmonic_energy_constant hr
  refine ⟨Real.sqrt A, Real.sqrt_pos.mpr hA, ?_⟩
  intro E u g M hu hw hM hb
  have henergy := hbound hu hw hM hb
  have hgI : Integrable (fun x => ‖g x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hu.2.1.1).mp hu.2.1
  have hball : (∫ x in Metric.ball (0 : Plane) (2*r), ‖g x‖ ^ 2) ≤
      ∫ x in Metric.closedBall (0 : Plane) (2*r), ‖g x‖ ^ 2 := by
    apply setIntegral_mono_set hgI.integrableOn
    · exact ae_of_all _ fun x => sq_nonneg _
    · exact ae_of_all _ fun x hx => Metric.ball_subset_closedBall hx
  have heq : eLpNorm g 2 (volume.restrict (Metric.ball (0 : Plane) (2*r))) =
      ENNReal.ofReal (Real.sqrt (∫ x in Metric.ball (0 : Plane) (2*r), ‖g x‖ ^ 2)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow, one_div] using
      MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hu.2.1.restrict (Metric.ball (0 : Plane) (2*r)))
  rw [eLpNorm_indicator_eq_eLpNorm_restrict Metric.isOpen_ball.measurableSet, heq,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (A * M ^ 2) := Real.sqrt_le_sqrt (hball.trans henergy)
    _ = Real.sqrt A * M := by rw [Real.sqrt_mul hA.le, Real.sqrt_sq_eq_abs, abs_of_nonneg hM]

end Torsion

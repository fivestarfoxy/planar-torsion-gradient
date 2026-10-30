module

public import Torsion.HalfPlaneGreen
public import Torsion.SobolevCore
public import Torsion.PolarIntegrability
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Weak source normalization of the logarithmic fundamental solution

The polar Jacobian cancels the reciprocal radial gradient. Radial FTC then
identifies the source mass against actual smooth compactly supported tests.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Torsion.HalfPlane

private def direction (θ : ℝ) : Plane := Complex.exp ((θ : Plane) * Complex.I)

private theorem direction_norm (θ : ℝ) : ‖direction θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

private theorem radial_hasDerivAt {ψ : Plane → ℝ} (hψ : Differentiable ℝ ψ)
    (θ r : ℝ) :
    HasDerivAt (fun t : ℝ => ψ ((t : Plane) * direction θ))
      (inner (𝕜 := ℝ) (gradient ψ ((r : Plane) * direction θ)) (direction θ)) r := by
  convert (hasGradientAt_iff_hasFDerivAt.mp
    (hψ ((r : Plane) * direction θ)).hasGradientAt).comp_hasDerivAt r
      (Complex.ofRealCLM.hasDerivAt.mul_const (direction θ)) using 1 <;>
  simp [InnerProductSpace.toDual_apply_apply, Function.comp_def]

private theorem fundamental_polar_pairing {r θ : ℝ} (hr : 0 < r) (v : Plane) :
    r * inner (𝕜 := ℝ)
      (gradient (fundamental 0) ((r : Plane) * direction θ)) v =
        -(2 * Real.pi)⁻¹ * inner (𝕜 := ℝ) v (direction θ) := by
  have hd : direction θ ≠ 0 := Complex.exp_ne_zero _
  have hr' : (r : Plane) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [(fundamental_hasGradientAt (by simpa using mul_ne_zero hr' hd)).gradient]
  have hi : star (((r : Plane) * direction θ)-0)⁻¹ = r⁻¹ • direction θ := by
    rw [Complex.inv_def]
    simp only [sub_zero, map_mul, star_star, Complex.star_def, Complex.conj_ofReal,
      Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      direction_norm, mul_one, abs_of_pos hr, mul_pow, one_pow, mul_one]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, div_eq_mul_inv, smul_eq_mul]
    all_goals field_simp [hr.ne'] <;> simp [← Complex.ofReal_pow] <;> ring
  rw [hi, real_inner_smul_left, real_inner_smul_left, real_inner_comm v]
  field_simp

private def radialPairing (ψ : Plane → ℝ) (p : ℝ × ℝ) : ℝ :=
  inner (𝕜 := ℝ) (gradient ψ ((p.1 : Plane) * direction p.2)) (direction p.2)

private theorem radialPairing_continuous {ψ : Plane → ℝ} (hψ : Continuous (gradient ψ)) :
    Continuous (radialPairing ψ) := by
  unfold radialPairing direction
  fun_prop

private theorem radialPairing_integral {ψ : Plane → ℝ} (hψ : Differentiable ℝ ψ)
    (hc : Continuous (gradient ψ)) {R : ℝ} (hR : 0 ≤ R)
    (hzero : ∀ z : Plane, R ≤ ‖z‖ → ψ z = 0) (θ : ℝ) :
    (∫ r in Ioc (0 : ℝ) R, radialPairing ψ (r, θ)) = -ψ 0 := by
  have hcont : Continuous (fun r : ℝ => radialPairing ψ (r, θ)) :=
    (radialPairing_continuous hc).comp (continuous_id.prodMk continuous_const)
  rw [← intervalIntegral.integral_of_le hR]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f' := fun r => radialPairing ψ (r,θ))
    (fun r _ => radial_hasDerivAt hψ θ r) (hcont.intervalIntegrable 0 R)]
  simp only [Complex.ofReal_zero, zero_mul]
  rw [hzero _ (by simp [norm_mul, direction_norm, abs_of_nonneg hR])]
  ring

/-- The source coefficient against every actual compact smooth planar test is
exactly one. This is the weak flux identity for the logarithmic fundamental
solution, proved by polar change of variables and ordinary radial FTC. -/
theorem fundamental_weak_source {D : Set Plane} {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    (∫ z : Plane, inner (𝕜 := ℝ) (gradient (fundamental 0) z) (gradient ψ z)) = ψ 0 := by
  obtain ⟨R, hR, hbound⟩ := hψ.2.1.isCompact.isBounded.exists_pos_norm_lt
  have hzero (z : Plane) (hz : R ≤ ‖z‖) : ψ z = 0 := by
    by_contra h
    exact (not_lt_of_ge hz) (hbound z (subset_tsupport ψ (Function.mem_support.mpr h)))
  have hgradzero (z : Plane) (hz : R ≤ ‖z‖) : gradient ψ z = 0 := by
    apply gradient_eq_zero_of_not_mem_tsupport
    exact fun h => (not_lt_of_ge hz) (hbound z h)
  let S := Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  have hS : S ⊆ polarCoord.target := fun p hp => ⟨hp.1.1, hp.2⟩
  have hKI : IntegrableOn (radialPairing ψ) S := by
    apply ((radialPairing_continuous hψ.continuous_gradient).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
    exact fun p hp => ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hrestrict : (∫ p in polarCoord.target, radialPairing ψ p) =
      ∫ p in S, radialPairing ψ p := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero polarCoord.open_target.measurableSet hS
    intro p hp
    have hrp : R < p.1 := by
      by_contra h
      exact hp.2 ⟨⟨hp.1.1, le_of_not_gt h⟩, hp.1.2⟩
    unfold radialPairing
    rw [hgradzero _ (by simp [norm_mul, direction_norm, abs_of_pos (show 0 < p.1 from hp.1.1)]; exact hrp.le), inner_zero_left]
  have hKIswap : IntegrableOn (fun p : ℝ × ℝ => radialPairing ψ (p.2,p.1))
      (Ioo (-Real.pi) Real.pi ×ˢ Ioc (0 : ℝ) R) := by
    have h := hKI
    simp only [IntegrableOn, S, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    simpa only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] using! h.swap
  have hinter : (∫ p in S, radialPairing ψ p) =
      ∫ θ in Ioo (-Real.pi) Real.pi, ∫ r in Ioc (0 : ℝ) R, radialPairing ψ (r,θ) := by
    change (∫ p in Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi, radialPairing ψ p) = _
    rw [Measure.volume_eq_prod, ← setIntegral_prod_swap,
      setIntegral_prod _ (by simpa only [Measure.volume_eq_prod, Function.comp_def] using! hKIswap)]
    rfl
  rw [← Complex.integral_comp_polarCoord_symm]
  calc
    _ = ∫ p in polarCoord.target, -(2 * Real.pi)⁻¹ * radialPairing ψ p := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      have hpole : Complex.polarCoord.symm p = (p.1 : Plane) * direction p.2 := by
        simp [Complex.polarCoord_symm_apply, direction, Complex.exp_mul_I]
      dsimp only
      rw [hpole]
      exact fundamental_polar_pairing hp.1 _
    _ = -(2 * Real.pi)⁻¹ * ∫ p in polarCoord.target, radialPairing ψ p := integral_const_mul _ _
    _ = -(2 * Real.pi)⁻¹ * ∫ p in S, radialPairing ψ p := by rw [hrestrict]
    _ = -(2 * Real.pi)⁻¹ * (∫ θ in Ioo (-Real.pi) Real.pi, -ψ 0) := by
      rw [hinter]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ _
      exact radialPairing_integral (hψ.1.differentiable (by simp)) hψ.continuous_gradient hR.le hzero θ
    _ = ψ 0 := by
      simp only [setIntegral_const, Real.volume_real_Ioo_of_le
        (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]), sub_neg_eq_add, smul_eq_mul]
      field_simp
      ring

/-- The weak source pairing is an actual integrable function; no cancellation
of nonintegrable Bochner integrals is used in subsequent Green identities. -/
theorem fundamental_pairing_integrable {D : Set Plane} {ψ : Plane → ℝ} (hψ : IsTest D ψ) :
    Integrable (fun z : Plane =>
      inner (𝕜 := ℝ) (gradient (fundamental 0) z) (gradient ψ z)) := by
  obtain ⟨R, hR, hbound⟩ := hψ.2.1.isCompact.isBounded.exists_pos_norm_lt
  have hgradzero (z : Plane) (hz : R ≤ ‖z‖) : gradient ψ z = 0 := by
    apply gradient_eq_zero_of_not_mem_tsupport
    exact fun h => (not_lt_of_ge hz) (hbound z h)
  let S := Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  have hKI : IntegrableOn (radialPairing ψ) S := by
    apply ((radialPairing_continuous hψ.continuous_gradient).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
    exact fun p hp => ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hKtarget : IntegrableOn (radialPairing ψ) polarCoord.target := by
    apply hKI.of_forall_diff_eq_zero polarCoord.open_target.measurableSet
    intro p hp
    have hrp : R < p.1 := by
      by_contra h
      exact hp.2 ⟨⟨hp.1.1, le_of_not_gt h⟩, hp.1.2⟩
    unfold radialPairing
    rw [hgradzero _ (by
      simp [norm_mul, direction_norm, abs_of_pos (show 0 < p.1 from hp.1.1)]
      exact hrp.le), inner_zero_left]
  apply (integrable_iff_complex_polar _).mpr
  apply IntegrableOn.congr_fun (hKtarget.const_mul (-(2 * Real.pi)⁻¹)) _
    polarCoord.open_target.measurableSet
  intro p hp
  have hpole : Complex.polarCoord.symm p = (p.1 : Plane) * direction p.2 := by
    simp [Complex.polarCoord_symm_apply, direction, Complex.exp_mul_I]
  dsimp only
  rw [hpole]
  exact (fundamental_polar_pairing hp.1 _).symm

end Torsion.HalfPlane

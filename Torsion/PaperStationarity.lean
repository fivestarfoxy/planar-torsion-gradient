module

public import Torsion.CanonicalSpectralCandidate
public import Torsion.CauchyHadamardBoundaryIntegral
public import Torsion.ShapeForcing

@[expose] public section

/-! # First variations for local deformations of the physical domain -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff

namespace Torsion.Shape

/-- The derivative of the actual Lebesgue area under a compact smooth
deformation is the integral of its divergence. The domain need only be
bounded and measurable. -/
theorem volume_deformation_hasDerivAt {D : Set Plane} (hD : MeasurableSet D)
    (hB : Bornology.IsBounded D) {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) :
    HasDerivAt (fun t : ℝ => volume.real (deformation V t '' D))
      (∫ z in D, divergence V z) 0 := by
  let J := fun z => (fderiv ℝ V z).det
  have hJc : Continuous J := ContinuousLinearMap.continuous_det.comp (hV.continuous_fderiv (by simp))
  have hiJ : IntegrableOn J D :=
    (hJc.continuousOn.integrableOn_compact hB.isCompact_closure).mono_set subset_closure
  have hid : IntegrableOn (divergence V) D :=
    ((divergence_continuous hV).continuousOn.integrableOn_compact hB.isCompact_closure).mono_set subset_closure
  have hi1 : IntegrableOn (fun _ : Plane => (1 : ℝ)) D :=
    (continuousOn_const.integrableOn_compact hB.isCompact_closure).mono_set subset_closure
  have hd := ((hasDerivAt_const (0:ℝ) (volume.real D)).add
    ((hasDerivAt_id 0).mul_const (∫ z in D, divergence V z))).add
    (((hasDerivAt_id 0).pow 2).mul_const (∫ z in D, J z))
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_zero,
    zero_mul, add_zero, zero_add, mul_one, one_mul] at hd
  apply hd.congr_of_eventuallyEq
  obtain ⟨δ, hδ, hhomeo⟩ := exists_deformationHomeomorph_of_contDiff_compact hV hVc
  obtain ⟨η, hη, hdet⟩ := exists_uniform_jacobian_half_le hV hVc
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (lt_min hδ hη)] with t ht
  have ht' : |t| < min δ η := by simpa [Metric.mem_ball, Real.dist_eq] using ht
  obtain ⟨e, he⟩ := hhomeo t (lt_of_lt_of_le ht' (min_le_left _ _))
  have hinj : InjOn (deformation V t) D := he ▸ e.injective.injOn
  have hf (z : Plane) (_hz : z ∈ D) : HasFDerivWithinAt (deformation V t)
      (fderiv ℝ (deformation V t) z) D z :=
    ((deformation_contDiff hV t).differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt
  have hjac := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hD hf hinj
    (fun _ : Plane => (1 : ℝ))
  simp only [smul_eq_mul, mul_one, integral_const, measureReal_def, Measure.restrict_apply_univ] at hjac
  calc
    volume.real (deformation V t '' D) = _ := hjac
    _ = ∫ z in D, 1 + t * divergence V z + t ^ 2 * J z := by
      apply setIntegral_congr_fun hD
      intro z _
      have hsign := hdet t (lt_of_lt_of_le ht' (min_le_right _ _)) z
      change |LinearMap.det (fderiv ℝ (deformation V t) z).toLinearMap| = _
      rw [abs_of_nonneg (by linarith), det_fderiv_deformation ((hV.differentiable (by simp)) z) t,
        jacobian_polynomial, realMatrix_det, trace_realMatrix]
      rfl
    _ = _ := by
      have hsplit := integral_add (hi1.add (hid.const_mul t)) (hiJ.const_mul (t ^ 2))
      simp only [Pi.add_apply] at hsplit
      rw [hsplit, integral_add hi1 (hid.const_mul t), integral_const_mul, integral_const_mul]
      simp

end Torsion.Shape

namespace Torsion.Spectral

/-- For every smooth vector field supported away from the flat boundary, the
flux variation is the explicit stationary factor times the total normal
speed on the free arc. -/
theorem second_localized_flux_hasDerivAt {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (hVU : tsupport V ⊆ upperHalfPlane) :
    HasDerivAt (fun t : ℝ => torsionFlux (Shape.deformation V t '' cauchyImage secondEigenfunction))
      (secondMoments.stationarity * ∫ s in Icc (-1 : ℝ) 1,
        inner (𝕜 := ℝ) (V (cauchyExtension secondEigenfunction (s : Plane)))
          (cauchyOutwardNormal secondEigenfunction s) *
            ‖cauchyDerivativeExtension secondEigenfunction (s : Plane)‖) 0 := by
  have ha := secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
  have h := torsionFlux_cauchy_boundary_hadamard secondEigenfunction_isRestrictedEigenfunction
    ha secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation hV hVc hVU
  rw [← integral_const_mul]
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  have hn := norm_ne_zero_iff.mpr (cauchyDerivativeExtension_ne_zero_on_interval ha
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation hs)
  simp only [Moments.stationarity, secondMoments_a, secondMoments_M]
  have hM : mass secondEigenfunction ≠ 0 := secondMoments.M_pos.ne'
  field_simp [ha.ne', hM, hn]

end Torsion.Spectral

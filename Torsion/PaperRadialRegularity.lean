module

public import Torsion.CanonicalSpectralCandidate
public import Torsion.CauchyRadialHadamardDensity
public import Torsion.CauchyShapeBoundaryData

@[expose] public section

/-! # Analyticity of the free arc in polar angle -/

noncomputable section
open Set Filter
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral

/-- Restricting the holomorphic extension to the parameter axis gives a
real-analytic parametrization at every open-arc point. -/
theorem IsRestrictedEigenfunction.cauchyBoundary_analyticAt
    {a : ℝ} {φ : ℝ → ℝ} (hEig : IsRestrictedEigenfunction a φ)
    (hodd : Function.Odd φ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    AnalyticAt ℝ (fun s : ℝ => cauchyExtension φ (s : Plane)) t := by
  obtain ⟨r, hr, A, hAd, hA⟩ := hEig.exists_height_Cauchy_extension_of_odd hodd t ht
  have hAa : AnalyticAt ℂ A (t : Plane) := hAd.analyticAt (Metric.ball_mem_nhds _ hr)
  have hAr : ContDiffAt ℝ ω (fun s : ℝ => A (s : Plane)) t :=
    ((hAa.contDiffAt (n := ω)).restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt
  apply (hAr.congr_of_eventuallyEq ?_).analyticAt
  filter_upwards [Metric.ball_mem_nhds t hr] with s hs
  symm
  apply hA
  refine ⟨?_, by simp⟩
  simpa only [Metric.mem_ball, Complex.isometry_ofReal.dist_eq] using hs

set_option maxHeartbeats 600000 in
/-- The paper's radius is real analytic in its polar angle on the open
upper semicircle. The positive angular derivative supplies an analytic
local inverse of the boundary parametrization. -/
theorem secondRadialProfile_analyticOnNhd :
    AnalyticOnNhd ℝ (fun θ : ℝ => ContinuousProfiles.extend secondRadialProfile θ)
      (Ioo 0 Real.pi) := by
  let γ := fun s : ℝ => cauchyExtension secondEigenfunction (s : ℂ)
  let Θ := fun s : ℝ => (γ s).arg
  let H := cauchyAngleHomeomorph secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation
    secondEigenfunction_concaveOn_Ioo secondEigenfunction_differentiableAt_positive
  have hends := cauchy_boundary_arg_endpoints secondHolderConstant_spec half_pos_nnreal
    half_le_one_nnreal secondEigenfunction_odd secondEigenfunction_zero_exterior secondEigenfunction_pos
  intro θ hθ
  let θ' : ContinuousProfiles.Angle := ⟨θ, Ioo_subset_Icc_self hθ⟩
  let p := H.symm θ'
  let t : ℝ := p.val
  have he : Θ t = θ := congrArg Subtype.val (H.apply_symm_apply θ')
  have ht : t ∈ Ioo (-1 : ℝ) 1 := by
    have hb : t ∈ Icc (-1 : ℝ) 1 := p.property
    refine ⟨lt_of_le_of_ne hb.1 ?_, lt_of_le_of_ne hb.2 ?_⟩
    · intro h
      have h0 : Θ (-1) = 0 := by simpa [Θ, γ] using hends.1
      rw [← h, h0] at he
      linarith [hθ.1]
    · intro h
      have hπ : Θ 1 = Real.pi := by simpa [Θ, γ] using hends.2
      rw [h, hπ] at he
      linarith [hθ.2]
  have hγ : ContDiffAt ℝ ω γ t :=
    (secondEigenfunction_isRestrictedEigenfunction.cauchyBoundary_analyticAt secondEigenfunction_odd ht).contDiffAt
  have him : 0 < (γ t).im := by
    change 0 < (cauchyExtension secondEigenfunction (t : ℂ)).im
    simpa [cauchyExtension_ofReal] using
      (height_pos secondEigenfunction_continuous.continuousOn secondEigenfunction_pos (abs_lt.mpr ht))
  have hslit := Complex.mem_slitPlane_iff.mpr (Or.inr him.ne')
  have hang : ContDiffAt ℝ ω Θ t := by
    have hlog := ((Complex.contDiffAt_log (n := ω) hslit).restrict_scalars ℝ).comp t hγ
    simpa only [Θ, Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
      (Complex.imCLM.contDiff.contDiffAt.comp t hlog)
  have hd := cauchy_boundary_arg_hasDerivAt secondHolderConstant_spec half_pos_nnreal
    half_le_one_nnreal secondEigenfunction_odd secondEigenfunction_zero_exterior secondEigenfunction_pos
    secondBoundaryConstant_equation ht
  have hsupport := cauchySupport_origin_pos secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation
    secondEigenfunction_concaveOn_Ioo secondEigenfunction_differentiableAt_positive ht
  have hn : γ t ≠ 0 := by intro h; rw [h] at him; exact lt_irrefl _ him
  have hdpos := div_pos hsupport (sq_pos_of_pos (norm_pos_iff.mpr hn))
  have hstrict := (hang.hasStrictDerivAt' hd (by simp)).hasStrictFDerivAt_equiv hdpos.ne'
  let K := hang.localInverse hstrict.hasFDerivAt (by simp)
  have hK : ContDiffAt ℝ ω K (Θ t) := hang.to_localInverse hstrict.hasFDerivAt (by simp)
  have hKt : K (Θ t) = t := hang.localInverse_apply_image hstrict.hasFDerivAt (by simp)
  have hright : ∀ᶠ y in 𝓝 (Θ t), Θ (K y) = y :=
    (hang.hasStrictFDerivAt' hstrict.hasFDerivAt (by simp)).eventually_right_inverse
  have hnear : ∀ᶠ y in 𝓝 (Θ t), K y ∈ Ioo (-1 : ℝ) 1 := by
    apply hK.continuousAt.eventually
    apply isOpen_Ioo.mem_nhds
    rwa [hKt]
  rw [← he]
  have hnorm : ContDiffAt ℝ ω (fun s : ℝ => ‖γ s‖) t := hγ.norm ℝ hn
  have hnormK : ContDiffAt ℝ ω (fun s : ℝ => ‖γ s‖) (K (Θ t)) := by rwa [hKt]
  apply ((hnormK.comp (Θ t) hK).congr_of_eventuallyEq ?_).analyticAt
  filter_upwards [hright, hnear] with y hy hKy
  change ContinuousProfiles.extend secondRadialProfile y = ‖γ (K y)‖
  calc
   _ = ContinuousProfiles.extend secondRadialProfile (Θ (K y)) := congrArg _ hy.symm
   _ = _ := cauchyRadialProfile_extend_arg secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation
    secondEigenfunction_concaveOn_Ioo secondEigenfunction_differentiableAt_positive (Ioo_subset_Icc_self hKy)

end Torsion.Spectral

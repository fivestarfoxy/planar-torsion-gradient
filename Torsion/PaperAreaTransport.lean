module

public import Torsion.PaperStationarity
public import Torsion.CauchyImageAreaExhaustion
public import Torsion.CauchyConformalGeometry.CompactifiedClosure

@[expose] public section

/-! # Area transport on the canonical free arc

Green's rectangle formula on the conformal parameter plane identifies the
integral of the physical divergence with the oriented free-arc normal speed.
Compact support away from the flat side removes the three remote sides.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff Interval
namespace Torsion.Spectral

private abbrev position := cauchyExtension secondEigenfunction
private abbrev tangent := cauchyDerivativeExtension secondEigenfunction
private abbrev coordinates := Complex.equivRealProdCLM.symm
private abbrev integrand (V : Plane → Plane) (z : ℂ) :=
  ‖tangent z‖ ^ 2 * Shape.divergence V (position z)

private def field (V : Plane → Plane) (z : Plane) : Plane :=
  (starRingEnd ℂ) (V (position z)) * tangent z

private def fieldDerivative (V : Plane → Plane) (z : Plane) : Plane →L[ℝ] Plane :=
  (starRingEnd ℂ) (V (position z)) •
    (deriv (deriv (cauchy secondEigenfunction)) z • (1 : Plane →L[ℝ] Plane)) +
  tangent z • (Complex.conjCLE.toContinuousLinearMap.comp
    ((fderiv ℝ V (position z)).comp (tangent z • (1 : Plane →L[ℝ] Plane))))

private theorem field_hasFDerivAt {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    HasFDerivAt (field V) (fieldDerivative V z) z := by
  have hc := secondEigenfunction_continuous
  have hF := (hasDerivAt_cauchy hc.continuousOn hz).differentiableAt.hasDerivAt.complexToReal_fderiv
  have hD := ((cauchy_analyticOnNhd hc.continuousOn).deriv z hz).differentiableAt.hasDerivAt.complexToReal_fderiv
  have hC := Complex.conjCLE.hasFDerivAt.comp z
    (((hV.differentiable (by simp)) (cauchy secondEigenfunction z)).hasFDerivAt.comp z hF)
  have hd : HasFDerivAt (fun u => (starRingEnd ℂ) (V (cauchy secondEigenfunction u)) *
      deriv (cauchy secondEigenfunction) u) (fieldDerivative V z) z := by
    simpa only [fieldDerivative, position, tangent, cauchyExtension_eq hc.continuousOn hz,
      cauchyDerivativeExtension_eq hc secondEigenfunction_odd secondEigenfunction_zero_exterior hz,
      Function.comp_def, Pi.mul_def, Complex.conjCLE_apply] using! hC.mul hD
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with u hu
  simp only [field, position, tangent, cauchyExtension_eq hc.continuousOn hu,
    cauchyDerivativeExtension_eq hc secondEigenfunction_odd secondEigenfunction_zero_exterior hu]

private theorem field_divergence (V : Plane → Plane) (z : Plane) :
    (fieldDerivative V z 1).re - (fieldDerivative V z Complex.I).im = integrand V z := by
  let L := fderiv ℝ V (position z)
  let d := tangent z
  have hL (x : ℂ) : L x = x.re • L 1 + x.im • L Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add]
    apply congrArg L
    simp [Complex.real_smul]
  simp only [fieldDerivative, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, one_apply_eq_self,
    smul_eq_mul, mul_one]
  simp only [integrand, Shape.divergence, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  change _ + (d * (starRingEnd ℂ) (L d)).re - (_ + d * (starRingEnd ℂ) (L (d * Complex.I))).im = _
  rw [hL d, hL (d * Complex.I)]
  simp [Complex.real_smul, Complex.mul_re, Complex.mul_im]
  ring

private theorem rectangle {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in -R..R, ∫ y in (0 : ℝ)..R, integrand V ((x : ℂ) + (y : ℂ) * Complex.I)) =
    (((∫ x in -R..R, -(field V ((x : ℂ) + (R : ℂ) * Complex.I)).im) -
      ∫ x in -R..R, -(field V (x : ℂ)).im) +
      ∫ y in (0 : ℝ)..R, (field V ((R : ℂ) + (y : ℂ) * Complex.I)).re) -
      ∫ y in (0 : ℝ)..R, (field V ((-R : ℂ) + (y : ℂ) * Complex.I)).re := by
  let F := fun p : ℝ × ℝ => field V (coordinates p)
  let D := fun p : ℝ × ℝ => (fieldDerivative V (coordinates p)).comp coordinates.toContinuousLinearMap
  let K := Icc (-R) R ×ˢ Icc 0 R
  have hRR : -R ≤ R := by linarith
  have hc : MapsTo coordinates K (closure upperHalfPlane) := by
    intro p hp
    simpa only [upperHalfPlane, Complex.closure_setOfPred_lt_im, mem_ofPred_eq,
      Complex.equivRealProdCLM_symm_apply, Complex.add_im, Complex.ofReal_im,
      Complex.mul_I_im, Complex.ofReal_re, zero_add] using hp.2.1
  obtain ⟨hF, hT, _, _⟩ := cauchy_extensions_diffContOnCl_of_holder
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior
  have h1 := hF.continuousOn.comp coordinates.continuous.continuousOn hc
  have h2 := hT.continuousOn.comp coordinates.continuous.continuousOn hc
  have h3 : ContinuousOn F K := (Complex.continuous_conj.comp_continuousOn
    (hV.continuous.comp_continuousOn h1)).mul h2
  have hd (p : ℝ × ℝ) (hp : p ∈ Ioo (-R) R ×ˢ Ioo 0 R) : HasFDerivAt F (D p) p := by
    apply (field_hasFDerivAt hV ?_).comp p coordinates.hasFDerivAt
    simpa only [upperHalfPlane, mem_ofPred_eq, Complex.equivRealProdCLM_symm_apply,
      Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add] using hp.2.1
  have halg (p : ℝ × ℝ) : (Complex.reCLM.comp (D p)) (1,0) +
      ((-Complex.imCLM).comp (D p)) (0,1) = integrand V (coordinates p) := by
    simpa [D, coordinates, Complex.equivRealProdCLM_symm_apply, sub_eq_add_neg] using
      field_divergence V (coordinates p)
  have hi : IntegrableOn (fun p => (Complex.reCLM.comp (D p)) (1,0) +
      ((-Complex.imCLM).comp (D p)) (0,1)) K := by
    simp_rw [halg]
    exact ((h2.norm.pow 2).mul ((Shape.divergence_continuous hV).comp_continuousOn h1)).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have green := integral2_divergence_prod_of_hasFDerivAt (fun p => (F p).re) (fun p => -(F p).im)
    (fun p => Complex.reCLM.comp (D p)) (fun p => (-Complex.imCLM).comp (D p)) (-R) 0 R R
    (by simpa only [uIcc_of_le hRR, uIcc_of_le hR, Function.comp_def, Pi.neg_apply] using Complex.continuous_re.comp_continuousOn h3)
    (by simpa only [uIcc_of_le hRR, uIcc_of_le hR, Function.comp_def, Pi.neg_apply] using! ((-Complex.imCLM).continuous.comp_continuousOn h3))
    (fun p hp => Complex.reCLM.hasFDerivAt.comp p (hd p (by simpa only [min_eq_left hR, max_eq_right hR, min_eq_left hRR, max_eq_right hRR] using hp)))
    (fun p hp => (-Complex.imCLM).hasFDerivAt.comp p (hd p (by simpa only [min_eq_left hR, max_eq_right hR, min_eq_left hRR, max_eq_right hRR] using hp)))
    (by simpa only [uIcc_of_le hRR, uIcc_of_le hR, Function.comp_def, Pi.neg_apply] using hi)
  simpa only [halg, coordinates, Complex.equivRealProdCLM_symm_apply, F, Complex.ofReal_neg,
    Complex.ofReal_zero, zero_mul, add_zero] using green

private theorem rectangle_support {V : Plane → Plane} (hVU : tsupport V ⊆ upperHalfPlane) :
    ∃ R : ℝ, 1 < R ∧ ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ → position z ∉ tsupport V := by
  have hzero : (0 : ℂ) ∉ tsupport V := by
    intro h
    simpa [upperHalfPlane] using hVU h
  have hf := cauchy_tendsto_zero secondEigenfunction_continuous.continuousOn
    (tendsto_norm_cobounded_atTop : Tendsto norm (Bornology.cobounded ℂ) atTop)
  have he := hf.eventually ((isClosed_tsupport V).isOpen_compl.mem_nhds hzero)
  obtain ⟨r, _, hr⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp he
  refine ⟨max 2 r, lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun z hz hn => ?_⟩
  have hbig : 1 < ‖z‖ := by linarith [le_max_left (2:ℝ) r]
  rw [show position z = cauchy secondEigenfunction z from
    cauchyExtension_eq_of_closed_exterior secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal
      secondEigenfunction_odd secondEigenfunction_zero_exterior hz hbig]
  exact hr (le_trans (le_max_right _ _) hn)

private theorem outward_density (V : Plane → Plane) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    (field V (x : ℂ)).im =
      inner (𝕜 := ℝ) (V (position (x : ℂ))) (cauchyOutwardNormal secondEigenfunction x) *
        ‖tangent (x : ℂ)‖ := by
  have hd : ‖tangent (x : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr
    (cauchyDerivativeExtension_ne_zero_on_interval secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
      secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
      secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation hx)
  rw [cauchyOutwardNormal, cauchyInwardNormal, inner_neg_right, real_inner_smul_right]
  change _ = -(‖tangent (x : ℂ)‖⁻¹ * _) * ‖tangent (x : ℂ)‖
  field_simp [hd]
  simp [field, Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

private theorem freeArc_integral_divergence {V : Plane → Plane} (hV : ContDiff ℝ ∞ V)
    (hVU : tsupport V ⊆ upperHalfPlane) :
    (∫ w in cauchyImage secondEigenfunction, Shape.divergence V w) =
      ∫ x in Icc (-1 : ℝ) 1, inner (𝕜 := ℝ) (V (position (x : ℂ)))
        (cauchyOutwardNormal secondEigenfunction x) * ‖tangent (x : ℂ)‖ := by
  obtain ⟨R, hR, hr⟩ := rectangle_support hVU
  have hR0 : 0 ≤ R := by linarith
  have hRR : -R ≤ R := by linarith
  have hH : IsOpen upperHalfPlane := isOpen_lt continuous_const Complex.continuous_im
  have hD := secondCauchyDomain.bounded.isCompact_closure
  have hiD : IntegrableOn (Shape.divergence V) (cauchyImage secondEigenfunction) :=
    ((Shape.divergence_continuous hV).continuousOn.integrableOn_compact hD).mono_set subset_closure
  have hd (z : ℂ) (hz : z ∈ upperHalfPlane) :=
    (hasDerivAt_cauchy secondEigenfunction_continuous.continuousOn hz).differentiableAt.hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt
      (s := upperHalfPlane)
  have hinj := cauchy_injOn_upperHalfPlane secondEigenfunction_continuous secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos
  have heq := integral_image_eq_integral_abs_det_fderiv_smul volume hH.measurableSet hd hinj
    (Shape.divergence V)
  have hi := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    hH.measurableSet hd hinj (Shape.divergence V)).mp hiD
  simp only [complex_mul_real_det, abs_sq, smul_eq_mul] at heq hi
  have hparam (z : ℂ) (hz : z ∈ upperHalfPlane) : integrand V z =
      ‖deriv (cauchy secondEigenfunction) z‖ ^ 2 * Shape.divergence V (cauchy secondEigenfunction z) := by
    simp only [integrand, tangent, position, cauchyExtension_eq secondEigenfunction_continuous.continuousOn hz,
      cauchyDerivativeExtension_eq secondEigenfunction_continuous secondEigenfunction_odd secondEigenfunction_zero_exterior hz]
  have hi' : IntegrableOn (integrand V) upperHalfPlane :=
    hi.congr (Filter.EventuallyEq.symm ((ae_restrict_mem hH.measurableSet).mono fun z hz => hparam z hz))
  have hbox : (∫ z in upperHalfPlane, integrand V z) = ∫ z in cauchyAreaRectangle R, integrand V z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hH.measurableSet (cauchyAreaRectangle_subset R)
    rintro z ⟨hz, hb⟩
    have hn : R ≤ ‖z‖ := by
      by_contra! hj
      apply hb
      have hx := abs_lt.mp ((Complex.abs_re_le_norm z).trans_lt hj)
      exact ⟨⟨hx.1, hx.2.le⟩, hz, (le_abs_self z.im).trans ((Complex.abs_im_le_norm z).trans hj.le)⟩
    have hvan := notMem_tsupport_iff_eventuallyEq.mp (hr z hz.le hn)
    have hder : fderiv ℝ V (position z) = 0 := by rw [hvan.fderiv_eq]; simp
    simp [integrand, Shape.divergence, hder]
  have hfield (x y : ℝ) (hy : 0 ≤ y) (hn : R ≤ |x| ∨ R ≤ |y|) :
      field V ((x : ℂ) + (y : ℂ) * Complex.I) = 0 := by
    let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
    have hre : z.re = x := by simp [z]
    have him : z.im = y := by simp [z]
    have hlo : R ≤ ‖z‖ := hn.elim
      (fun h => h.trans (hre ▸ Complex.abs_re_le_norm z))
      (fun h => h.trans (him ▸ Complex.abs_im_le_norm z))
    exact (by simp [field, image_eq_zero_of_notMem_tsupport (hr z (him ▸ hy) hlo)] :
      field V z = 0)
  have ht : (∫ x in -R..R, -(field V ((x : ℂ) + (R : ℂ) * Complex.I)).im) = 0 := by
    apply (intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) _).trans intervalIntegral.integral_zero
    intro x _
    simp [hfield x R hR0 (Or.inr (le_abs_self _))]
  have hside (r : ℝ) (hr' : R ≤ |r|) :
      (∫ y in (0:ℝ)..R, (field V ((r : ℂ) + (y : ℂ) * Complex.I)).re) = 0 := by
    apply (intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) _).trans intervalIntegral.integral_zero
    intro y hy
    simp [hfield r y (uIcc_of_le hR0 ▸ hy).1 (Or.inl hr')]
  have hg := rectangle hV hR0
  have hleft := hside (-R) (by rw [abs_neg]; exact le_abs_self R)
  simp only [Complex.ofReal_neg] at hleft
  rw [ht, hside R (le_abs_self _), hleft] at hg
  simp only [intervalIntegral.integral_neg, sub_neg_eq_add, zero_add, add_zero, sub_zero] at hg
  calc
   _ = ∫ z in upperHalfPlane, integrand V z :=
     heq.trans (setIntegral_congr_fun hH.measurableSet (fun z hz => (hparam z hz).symm))
   _ = _ := hbox
   _ = _ := integral_cauchyAreaRectangle_eq_iterated hR0 (hi'.mono_set (cauchyAreaRectangle_subset _))
   _ = _ := hg
   _ = ∫ x in Icc (-1:ℝ) 1, (field V (x : ℂ)).im := by
     rw [intervalIntegral.integral_of_le hRR, ← integral_Icc_eq_integral_Ioc]
     apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc (Icc_subset_Icc (by linarith) hR.le)
     rintro x ⟨_, hx⟩
     have hbig : 1 ≤ |x| := by
       by_contra! h
       exact hx (Ioo_subset_Icc_self (abs_lt.mp h))
     have him : (position (x:ℂ)).im = 0 := by simp [position, cauchyExtension_ofReal, height_zero_of_one_le_abs _ hbig]
     have hn : position (x:ℂ) ∉ tsupport V := by
       intro h
       have hp : 0 < (position (x:ℂ)).im := hVU h
       linarith
     simp [field, image_eq_zero_of_notMem_tsupport hn]
   _ = _ := setIntegral_congr_fun measurableSet_Icc (outward_density V)

/-- For an arbitrary local smooth displacement, the derivative of physical
Lebesgue area is the integral of its outward normal speed over the free arc. -/
theorem second_localized_area_hasDerivAt {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (hVU : tsupport V ⊆ upperHalfPlane) :
    HasDerivAt (fun t : ℝ => volume.real (Shape.deformation V t '' cauchyImage secondEigenfunction))
      (∫ x in Icc (-1 : ℝ) 1, inner (𝕜 := ℝ) (V (cauchyExtension secondEigenfunction (x : ℂ)))
        (cauchyOutwardNormal secondEigenfunction x) * ‖cauchyDerivativeExtension secondEigenfunction (x : ℂ)‖) 0 := by
  rw [← freeArc_integral_divergence hV hVU]
  exact Shape.volume_deformation_hasDerivAt secondCauchyDomain.isOpen.measurableSet secondCauchyDomain.bounded hV hVc

/-- The physical, area-constrained Lagrangian is stationary for every
compact smooth displacement supported above the flat side. -/
theorem second_localized_lagrangian_stationary {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (hVU : tsupport V ⊆ upperHalfPlane) :
    HasDerivAt (fun t : ℝ => torsionFlux (Shape.deformation V t '' cauchyImage secondEigenfunction) -
      secondMoments.stationarity * volume.real (Shape.deformation V t '' cauchyImage secondEigenfunction)) 0 0 := by
  simpa only [sub_self, Pi.sub_def] using!
    (second_localized_flux_hasDerivAt hV hVc hVU).sub
      ((second_localized_area_hasDerivAt hV hVc hVU).const_mul secondMoments.stationarity)

/-- Any physical deformation preserving area to first order has zero
first variation of the actual marked torsion flux. -/
theorem second_localized_stationary_of_area_preserving {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (hVU : tsupport V ⊆ upperHalfPlane)
    (harea : HasDerivAt (fun t : ℝ =>
      volume.real (Shape.deformation V t '' cauchyImage secondEigenfunction)) 0 0) :
    HasDerivAt (fun t : ℝ => torsionFlux (Shape.deformation V t '' cauchyImage secondEigenfunction)) 0 0 := by
  have hz := (second_localized_area_hasDerivAt hV hVc hVU).unique harea
  simpa only [hz, mul_zero] using second_localized_flux_hasDerivAt hV hVc hVU

end Torsion.Spectral

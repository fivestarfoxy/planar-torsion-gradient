module

public import Torsion.CanonicalSpectralCandidate
public import Torsion.PaperGeometryReflection
public import Torsion.PaperRadialRegularity
public import Torsion.PaperAreaTransport
public import Torsion.PaperHilbertCoefficient
public import Torsion.CauchyConformalGeometry.BoundaryCurvature
public import Torsion.CauchyConformalGeometry.ConvexitySlope

@[expose] public section

/-! # Curvature and tangencies of the canonical free arc

The determinant estimate on the positive half extends to the reflected half by
parity. At the crest the slope of the odd profile is strictly positive, as
follows from its tangent at zero and any interior positive value. -/

noncomputable section
open Set MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The explicit endpoint integral for the constant of the normalized
second eigenfunction. Absolute integrability follows from the spectral
square-root barrier. -/
theorem secondBoundaryConstant_endpoint_integral :
    secondBoundaryConstant = 2 / Real.pi *
      ∫ s in (0 : ℝ)..1, s * secondEigenfunction s / (1 - s ^ 2) := by
  apply boundaryConstant_endpoint_integral secondHolderConstant_spec half_pos_nnreal
    secondEigenfunction_odd secondEigenfunction_zero_exterior secondBoundaryConstant_equation
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  apply secondEigenfunction_endpoint_quotient_integrable.mono'
    (secondEigenfunction_continuous.measurable.div (measurable_const.sub measurable_id)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  change ‖secondEigenfunction s / (1 - s)‖ ≤ _
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (sub_pos.mpr hs.2)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (sub_pos.mpr (abs_lt.mpr hs))
    (sub_le_sub_left (le_abs_self s) _)

/-- The half-width is strictly positive, and the two ends of the canonical
arc are the real points at the positive and negative half-width. -/
theorem secondFreeArc_endpoints :
    let ℓ := Real.pi⁻¹ * ∫ s in Icc (-1 : ℝ) 1, height secondEigenfunction s / (1 - s)
    0 < ℓ ∧ cauchyExtension secondEigenfunction (-1 : ℂ) = (ℓ : ℂ) ∧
      cauchyExtension secondEigenfunction (1 : ℂ) = -(ℓ : ℂ) := by
  dsimp only
  rw [← cauchyEndpoint_halfWidth_integral]
  obtain ⟨hLim, hRim, _, hRre⟩ := cauchy_boundary_endpoints secondHolderConstant_spec
    half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd secondEigenfunction_zero_exterior
    secondEigenfunction_pos
  have hodd := cauchy_boundary_re_odd secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal
    secondEigenfunction_odd secondEigenfunction_zero_exterior (1 : ℝ)
  refine ⟨neg_pos.mpr hRre, Complex.ext ?_ ?_, Complex.ext ?_ ?_⟩
  · simpa only [Complex.ofReal_neg, Complex.ofReal_one, Complex.neg_re, Complex.ofReal_re] using hodd
  · simpa using hLim
  · simp
  · simpa using hRim

/-- The first derivative of the normalized profile is strictly positive at the crest. -/
theorem secondEigenfunction_deriv_zero_pos : 0 < deriv secondEigenfunction 0 := by
  have hzero : secondEigenfunction 0 = 0 := by
    have h := secondEigenfunction_odd 0
    rw [neg_zero] at h
    linarith
  have hdiff := (secondEigenfunction_analyticOnNhd 0 (by constructor <;> norm_num)).differentiableAt
  have ht := Curvature.concave_le_tangent secondEigenfunction_concaveOn
    (x := 0) (y := 1 / 2) (by constructor <;> norm_num) (by constructor <;> norm_num)
    hdiff.hasDerivAt
  rw [hzero] at ht
  linarith [secondEigenfunction_pos (1 / 2) (by constructor <;> norm_num)]

private theorem secondBoundaryVelocity_zero_neg :
    boundaryVelocity secondEigenvalue secondBoundaryConstant secondEigenfunction 0 < 0 := by
  have h := boundaryVelocity_zero_le_negative_half_height
    secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos secondEigenfunction_continuous.continuousOn
    secondEigenfunction_odd secondEigenfunction_zero_exterior secondEigenfunction_pos secondMoment_identity
  have hY : 0 < height secondEigenfunction 0 :=
    height_pos secondEigenfunction_continuous.continuousOn secondEigenfunction_pos (by norm_num)
  linarith [mul_pos secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos hY]

private theorem curvatureExpression_even {a b : ℝ} {φ : ℝ → ℝ} (hodd : Function.Odd φ) :
    Function.Even (fun t => a * (φ t) ^ 2 - boundaryVelocity a b φ t * deriv φ t) := by
  intro t
  have hcomp : (fun s : ℝ => φ (-s)) = -φ := funext hodd
  have hd := deriv_comp_neg φ t
  rw [hcomp, deriv.neg] at hd
  change a * (φ (-t)) ^ 2 - (b - a * height φ (-t)) * deriv φ (-t) =
    a * (φ t) ^ 2 - (b - a * height φ t) * deriv φ t
  rw [hodd t, height_even φ t, (neg_inj.mp hd).symm]
  ring

/-- The signed determinant is positive on the whole open free arc of the
constructed Cauchy map, including the crest. -/
theorem secondFreeArc_curvatureNumerator_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 < (star (cauchyDerivativeExtension secondEigenfunction (t : ℂ)) *
      deriv (fun s : ℝ => cauchyDerivativeExtension secondEigenfunction (s : ℂ)) t).im := by
  rw [cauchy_boundary_curvature_eq secondHolderConstant_spec half_pos_nnreal
    secondEigenfunction_odd secondEigenfunction_zero_exterior secondBoundaryConstant_equation
    (secondEigenfunction_analyticOnNhd t ht).differentiableAt ht]
  have hpos (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :=
    curvature_pos_of_holder_boundary_equation secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
      secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
      secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation
      secondEigenfunction_concaveOn_Ioo secondEigenfunction_differentiableAt_positive hs
  rcases lt_trichotomy t 0 with hlt | rfl | hgt
  · exact (hpos (-t) ⟨neg_pos.mpr hlt, by linarith [ht.1]⟩).trans_eq
      (curvatureExpression_even (a := secondEigenvalue) (b := secondBoundaryConstant)
        secondEigenfunction_odd t)
  · exact sub_pos.mpr ((mul_neg_of_neg_of_pos secondBoundaryVelocity_zero_neg
      secondEigenfunction_deriv_zero_pos).trans_le
      (mul_nonneg secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos.le (sq_nonneg _)))
  · exact hpos t ⟨hgt, ht.2⟩

/-- Signed Euclidean curvature, expressed with the first and second ordinary
derivatives of the actual parametrization and its speed cubed. -/
theorem secondFreeArc_signedCurvature_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    let γ := fun s : ℝ => cauchyExtension secondEigenfunction (s : ℂ)
    0 < (star (deriv γ t) * deriv (deriv γ) t).im / ‖deriv γ t‖ ^ 3 := by
  dsimp only
  have hγ : deriv (fun s : ℝ => cauchyExtension secondEigenfunction (s : ℂ)) =
      fun s : ℝ => cauchyDerivativeExtension secondEigenfunction (s : ℂ) :=
    funext fun s => (cauchy_boundary_hasDerivAt secondHolderConstant_spec half_pos_nnreal
      half_le_one_nnreal secondEigenfunction_odd secondEigenfunction_zero_exterior s).deriv
  rw [hγ]
  have hne := cauchyDerivativeExtension_ne_zero_on_interval
    secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos secondHolderConstant_spec
    half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd secondEigenfunction_zero_exterior
    secondEigenfunction_pos secondBoundaryConstant_equation (Ioo_subset_Icc_self ht)
  exact div_pos (secondFreeArc_curvatureNumerator_pos ht) (pow_pos (norm_pos_iff.mpr hne) _)

/-- The closed arc has horizontal tangents exactly at its two joins with
the flat side and at its crest. -/
theorem secondFreeArc_horizontalTangencies {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    (cauchyDerivativeExtension secondEigenfunction (t : ℂ)).im = 0 ↔
      t = -1 ∨ t = 0 ∨ t = 1 := by
  have him : (cauchyDerivativeExtension secondEigenfunction (t : ℂ)).im =
      -secondEigenfunction t := by simp [cauchyDerivativeExtension_ofReal]
  rw [him, neg_eq_zero]
  constructor
  · intro h
    by_cases hl : t = -1
    · exact Or.inl hl
    by_cases hr : t = 1
    · exact Or.inr (Or.inr hr)
    refine Or.inr (Or.inl ?_)
    rcases lt_trichotomy t 0 with hn | hz | hp
    · have hpos := secondEigenfunction_pos (-t) ⟨neg_pos.mpr hn, by
        linarith [lt_of_le_of_ne ht.1 (Ne.symm hl)]⟩
      rw [secondEigenfunction_odd t, h] at hpos
      linarith
    · exact hz
    · exact ((secondEigenfunction_pos t ⟨hp, lt_of_le_of_ne ht.2 hr⟩).ne' h).elim
  · rintro (rfl | rfl | rfl)
    · exact secondEigenfunction_zero_exterior _ (by norm_num)
    · have h := secondEigenfunction_odd 0
      rw [neg_zero] at h
      linarith
    · exact secondEigenfunction_zero_exterior _ (by norm_num)

/-- The two vertical tangents occur at opposite parameters. Their existence
and uniqueness use the moment equation and monotonicity of the actual
horizontal boundary velocity. -/
theorem secondFreeArc_verticalTangencies :
    ∃ τ ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      (cauchyDerivativeExtension secondEigenfunction (t : ℂ)).re = 0 ↔ t = τ ∨ t = -τ := by
  let v := boundaryVelocity secondEigenvalue secondBoundaryConstant secondEigenfunction
  obtain ⟨τ, ⟨hτ, hvτ⟩, _⟩ := existsUnique_boundaryVelocity_zero
    secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos secondEigenfunction_continuous
    secondEigenfunction_odd secondEigenfunction_zero_exterior secondEigenfunction_pos secondMoment_identity
  have hmono : StrictMonoOn v (Icc (0 : ℝ) 1) :=
    boundaryVelocity_strictMonoOn secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
      secondEigenfunction_continuous secondEigenfunction_odd secondEigenfunction_zero_exterior
      secondEigenfunction_pos
  have hv : Function.Even v := by
    intro s
    simp only [v, boundaryVelocity, height_even secondEigenfunction s]
  refine ⟨τ, hτ, ?_⟩
  intro t ht
  rw [cauchyDerivativeExtension_re_eq_boundaryVelocity secondHolderConstant_spec half_pos_nnreal
    secondEigenfunction_zero_exterior secondBoundaryConstant_equation t ht]
  change v t = 0 ↔ _
  constructor
  · intro h
    by_cases hsign : 0 ≤ t
    · exact Or.inl (hmono.injOn ⟨hsign, ht.2⟩ (Ioo_subset_Icc_self hτ) (h.trans hvτ.symm))
    · have heq := hmono.injOn
        (show -t ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith [ht.1]⟩)
        (Ioo_subset_Icc_self hτ) ((hv t).trans (h.trans hvτ.symm))
      exact Or.inr (by linarith)
  · rintro (rfl | rfl)
    · exact hvτ
    · exact (hv τ).trans hvτ

/-- The positive-parameter half of the free arc bends strictly to the left
of its endpoint chord in the horizontal coordinate. -/
theorem secondFreeArc_horizontalChord {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (cauchyExtension secondEigenfunction (t : ℂ)).re <
      t * (cauchyExtension secondEigenfunction (1 : ℂ)).re := by
  let X := fun s : ℝ => (cauchyExtension secondEigenfunction (s : ℂ)).re
  let v := boundaryVelocity secondEigenvalue secondBoundaryConstant secondEigenfunction
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt X (v s) s :=
    cauchy_boundary_re_hasDerivAt_velocity secondHolderConstant_spec half_pos_nnreal
      half_le_one_nnreal secondEigenfunction_odd secondEigenfunction_zero_exterior
      secondBoundaryConstant_equation ⟨by linarith [hs.1], hs.2⟩
  have hv : StrictMonoOn v (Icc (0 : ℝ) 1) :=
    boundaryVelocity_strictMonoOn secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
      secondEigenfunction_continuous secondEigenfunction_odd secondEigenfunction_zero_exterior
      secondEigenfunction_pos
  have hc : StrictConvexOn ℝ (Icc (0 : ℝ) 1) X := by
    apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc 0 1)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    intro s hs u hu hsu
    rw [(hd s (interior_subset hs)).deriv, (hd u (interior_subset hu)).deriv]
    exact hv (interior_subset hs) (interior_subset hu) hsu
  have hX0 : X 0 = 0 := by
    have h := cauchy_boundary_re_odd secondHolderConstant_spec half_pos_nnreal
      half_le_one_nnreal secondEigenfunction_odd secondEigenfunction_zero_exterior 0
    change X (-0) = -(X 0) at h
    rw [neg_zero] at h
    linarith
  have h := hc.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) (by norm_num)
    (sub_pos.mpr ht.2) ht.1 (by ring)
  change X t < t * X 1
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, hX0] using h

end Torsion.Spectral

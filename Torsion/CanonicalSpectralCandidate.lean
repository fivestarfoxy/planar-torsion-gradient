module

public import Torsion.RestrictedSpectralSecondHolder
public import Torsion.SpectralCandidate
public import Torsion.CauchyRadialDomain
public import Torsion.CauchyBoundaryStationarity

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual second spectral reference, without spectral hypotheses

The constructed second eigenfunction supplies the original moment record,
the original convex Cauchy domain, its actual weak torsion and marked flux,
and its positive continuous radial profile. Every compatibility field other
than the universal upper bound in `ReferenceCertificate` is proved here.
The final bridge constructor deliberately retains that global inequality as
an explicit argument: the geometric construction and signed stationarity
do not prove it.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace Torsion.Spectral

/-- A fixed Hölder constant for the actual normalized second profile. -/
def secondHolderConstant : ℝ≥0 := secondEigenfunction_holder_half.choose

theorem secondHolderConstant_spec :
    HolderWith secondHolderConstant (1 / 2) secondEigenfunction :=
  secondEigenfunction_holder_half.choose_spec

/-- The uniquely determined linear Hilbert coefficient of the actual
second eigenfunction, not an assumed spectral parameter. -/
def secondBoundaryConstant : ℝ :=
  secondEigenfunction_linear_hilbert_equation.exists.choose

theorem secondBoundaryConstant_equation (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    realCauchyBoundaryRe secondEigenfunction x =
      secondEigenvalue * height secondEigenfunction x - secondBoundaryConstant :=
  secondEigenfunction_linear_hilbert_equation.exists.choose_spec x hx

private theorem half_pos_nnreal : (0 : ℝ≥0) < 1 / 2 := by norm_num
private theorem half_le_one_nnreal : (1 / 2 : ℝ≥0) ≤ 1 := by norm_num

theorem secondEigenfunction_differentiableAt_positive (x : ℝ)
    (hx : x ∈ Ioo (0 : ℝ) 1) : DifferentiableAt ℝ secondEigenfunction x :=
  (secondEigenfunction_analyticOnNhd x ⟨by linarith [hx.1], hx.2⟩).differentiableAt

/-- The original positive moment record, constructed from the actual
second profile and the proved linear Hilbert equation. -/
def secondMoments : Moments :=
  momentsOfHolderBoundaryEquation secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation

@[simp] theorem secondMoments_a : secondMoments.a = secondEigenvalue := rfl
@[simp] theorem secondMoments_b : secondMoments.b = secondBoundaryConstant := rfl
@[simp] theorem secondMoments_M : secondMoments.M = mass secondEigenfunction := rfl
@[simp] theorem secondMoments_N : secondMoments.N = squareMass secondEigenfunction := rfl

theorem secondBoundaryConstant_pos : 0 < secondBoundaryConstant := secondMoments.b_pos

theorem secondMoment_identity :
    secondEigenvalue * squareMass secondEigenfunction =
      2 * secondBoundaryConstant * mass secondEigenfunction := secondMoments.moment

/-- The uniquely selected Hilbert coefficient is also an explicit ratio
of the original spectral moments. -/
theorem secondBoundaryConstant_eq_moments :
    secondBoundaryConstant = secondEigenvalue * squareMass secondEigenfunction /
      (2 * mass secondEigenfunction) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) secondMoments.M_pos.ne')).2
  change secondBoundaryConstant * (2 * mass secondEigenfunction) =
    secondEigenvalue * squareMass secondEigenfunction
  nlinarith [secondMoment_identity]

/-- The original concrete convex domain of the canonical second profile. -/
def secondCauchyDomain : ConvexDomain :=
  cauchyConvexDomain secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation
    secondEigenfunction_concaveOn_Ioo secondEigenfunction_differentiableAt_positive

@[simp] theorem secondCauchyDomain_carrier :
    secondCauchyDomain.carrier = cauchyImage secondEigenfunction := rfl

theorem secondCauchyDomain_isMarked : IsMarked secondCauchyDomain.carrier :=
  cauchyImage_isMarked secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal
    secondEigenfunction_odd secondEigenfunction_zero_exterior secondEigenfunction_pos

/-- This is the Euclidean area of the actual original image. -/
theorem secondCauchyDomain_area : secondCauchyDomain.area = secondMoments.area :=
  area_cauchyImage_eq_coefficient_mass
    secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos.ne'
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation

theorem secondCauchyDomain_area_spectral :
    secondCauchyDomain.area = secondEigenvalue * squareMass secondEigenfunction / 2 := by
  rw [secondCauchyDomain_area, secondMoments.area_eq]
  rfl

theorem secondCauchyDomain_isWeakTorsion :
    IsWeakTorsion secondCauchyDomain.carrier
      (physicalZeroExtension secondEigenfunction) (physicalZeroGradient secondEigenfunction) :=
  physicalCandidate_isWeakTorsion
    secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos.ne'
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation

theorem secondCauchyDomain_flux :
    torsionFlux secondCauchyDomain.carrier = secondMoments.flux :=
  torsionFlux_cauchyImage secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos.ne'
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation

theorem secondCauchyDomain_flux_moments :
    torsionFlux secondCauchyDomain.carrier =
      squareMass secondEigenfunction / (2 * mass secondEigenfunction) := by
  rw [secondCauchyDomain_flux, secondMoments.flux_eq]
  rfl

/-- The marked lower bound is for the actual essential gradient norm of
any actual weak Dirichlet theory, including the constructed one. -/
theorem secondCauchyDomain_marked_lower (T : DirichletTheory) :
    ENNReal.ofReal secondMoments.flux ≤ T.G secondCauchyDomain := by
  rw [← secondCauchyDomain_flux]
  exact T.torsionFlux_le_G secondCauchyDomain secondCauchyDomain_isMarked

/-- The actual radius of the original image, including the two joins. -/
def secondRadialProfile : ContinuousProfiles.Profile :=
  cauchyRadialProfile secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation
    secondEigenfunction_concaveOn_Ioo secondEigenfunction_differentiableAt_positive

theorem secondRadialProfile_pos (θ : ContinuousProfiles.Angle) :
    0 < secondRadialProfile θ :=
  cauchyRadialProfile_pos secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation
    secondEigenfunction_concaveOn_Ioo secondEigenfunction_differentiableAt_positive θ

theorem secondRadialProfile_domain :
    radialDomain (ContinuousProfiles.extend secondRadialProfile) = secondCauchyDomain.carrier :=
  radialDomain_cauchyRadialProfile_eq secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation
    secondEigenfunction_concaveOn_Ioo secondEigenfunction_differentiableAt_positive

theorem secondRadialProfile_norm_sq :
    ‖ContinuousProfiles.embed secondRadialProfile‖ ^ 2 =
      secondEigenvalue * squareMass secondEigenfunction :=
  norm_sq_embed_cauchyRadialProfile secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation
    secondEigenfunction_concaveOn_Ioo secondEigenfunction_differentiableAt_positive

theorem secondRadialProfile_euler :
    torsionFlux (radialDomain (ContinuousProfiles.extend secondRadialProfile)) =
      secondMoments.stationarity * ‖ContinuousProfiles.embed secondRadialProfile‖ ^ 2 := by
  rw [secondRadialProfile_domain, secondCauchyDomain_flux, secondRadialProfile_norm_sq]
  have he := secondMoments.euler
  rw [secondMoments.area_eq] at he
  simp only [secondMoments_a, secondMoments_N] at he
  calc
    secondMoments.flux = 2 * secondMoments.stationarity *
        (secondEigenvalue * squareMass secondEigenfunction / 2) := he
    _ = secondMoments.stationarity *
        (secondEigenvalue * squareMass secondEigenfunction) := by ring

/-- The concrete angular calibration density has the original spectral
stationarity factor and belongs to the actual angular L² space. Its being
a supporting functional still requires shape calculus. -/
def secondCalibrationDensity : ContinuousProfiles.ProfileL2 :=
  secondMoments.stationarity • ContinuousProfiles.embed secondRadialProfile

theorem secondCalibrationDensity_euler :
    inner (𝕜 := ℝ) secondCalibrationDensity
      (ContinuousProfiles.embed secondRadialProfile) =
      torsionFlux secondCauchyDomain.carrier := by
  rw [secondCalibrationDensity, real_inner_smul_left, real_inner_self_eq_norm_sq,
    ← secondRadialProfile_euler, secondRadialProfile_domain]

/-- The candidate L² calibration density has exactly the sharp spectral
normalization. No comparison with competing domains is used here. -/
theorem secondCalibrationDensity_constant :
    Real.sqrt 2 * ‖secondCalibrationDensity‖ =
      spectralConstant secondEigenvalue secondEigenfunction := by
  have hn : ‖ContinuousProfiles.embed secondRadialProfile‖ =
      Real.sqrt 2 * Real.sqrt secondMoments.area := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1
    rw [secondRadialProfile_norm_sq, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt secondMoments.area_pos.le, secondMoments.area_eq,
      secondMoments_a, secondMoments_N]
    ring
  rw [secondCalibrationDensity, norm_smul, Real.norm_eq_abs,
    abs_of_pos secondMoments.stationarity_pos, hn]
  calc
    Real.sqrt 2 * (secondMoments.stationarity *
        (Real.sqrt 2 * Real.sqrt secondMoments.area)) =
        (Real.sqrt 2) ^ 2 * secondMoments.stationarity * Real.sqrt secondMoments.area := by ring
    _ = 2 * secondMoments.stationarity * Real.sqrt secondMoments.area := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    _ = secondMoments.sharpConstant := secondMoments.calibration_constant_eq
    _ = spectralConstant secondEigenvalue secondEigenfunction := rfl

/-- The canonical weak torsion function and the concrete harmonic kernel
candidate satisfy signed stationarity along arbitrary physical interior
approaches, including both junctions. Green/Poisson normalization remains
a separate identification theorem. -/
theorem second_signed_stationarity {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun w =>
      (-inner (𝕜 := ℝ) (gradient (physicalCandidate secondEigenfunction) w)
        (cauchyOutwardNormal secondEigenfunction t)) *
      (-inner (𝕜 := ℝ) (gradient (physicalMarkedKernel secondEigenfunction) w)
        (cauchyOutwardNormal secondEigenfunction t)))
      (𝓝[secondCauchyDomain.carrier] (cauchyExtension secondEigenfunction (t : ℂ)))
      (𝓝 secondMoments.stationarity) :=
  signed_stationarity_physicalCandidate_kernel_tendsto_at_freeArc
    secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation ht

/-- The candidate lower bound is now completely unconditional: no spectral,
geometric, regularity, calibration or Dirichlet existence inputs remain. -/
theorem second_spectralConstant_le_cStar :
    ENNReal.ofReal (spectralConstant secondEigenvalue secondEigenfunction) ≤ torsionTheory.cStar :=
  secondEigenfunction_isRestrictedEigenfunction.spectralConstant_le_cStar
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_pos secondEigenfunction_concaveOn_Ioo
    secondEigenfunction_differentiableAt_positive

theorem second_normalized_cauchy_candidate :
    ∃ D : ConvexDomain, D.carrier = normalizedImage secondEigenvalue secondEigenfunction ∧
      D.area = 1 ∧ ENNReal.ofReal (spectralConstant secondEigenvalue secondEigenfunction) ≤
        torsionTheory.G D :=
  secondEigenfunction_isRestrictedEigenfunction.normalized_cauchy_candidate
    secondHolderConstant_spec half_pos_nnreal half_le_one_nnreal secondEigenfunction_odd
    secondEigenfunction_pos secondEigenfunction_concaveOn_Ioo
    secondEigenfunction_differentiableAt_positive

end Torsion.Spectral

namespace Torsion
open Spectral

/-- All reference fields except the substantial global upper bound are
constructed. The displayed remaining hypothesis is exactly the universal
calibrated estimate for the original full convex admissible class. -/
def secondReferenceCertificate_of_universal
    (huniversal : ∀ D : ConvexDomain, torsionTheory.G D ≤ ENNReal.ofReal
      (2 * secondMoments.stationarity * Real.sqrt secondMoments.area * Real.sqrt D.area)) :
    ReferenceCertificate torsionTheory secondMoments where
  domain := secondCauchyDomain
  area_eq := secondCauchyDomain_area
  marked_lower := secondCauchyDomain_marked_lower torsionTheory
  universal := huniversal

/-- This is an actual assembly of the existing bridge interface, conditional
only on its precise unresolved universal inequality. -/
def secondSpectralBridge_of_universal
    (huniversal : ∀ D : ConvexDomain, torsionTheory.G D ≤ ENNReal.ofReal
      (2 * secondMoments.stationarity * Real.sqrt secondMoments.area * Real.sqrt D.area)) :
    SpectralBridge torsionTheory secondEigenvalue secondEigenfunction where
  moments := secondMoments
  eigenvalue_eq := rfl
  mass_eq := rfl
  squareMass_eq := rfl
  reference := secondReferenceCertificate_of_universal huniversal
  image_eq := rfl

/-- The remaining global inequality alone would complete exact value and
attainment for the canonical actual second spectral construction. -/
theorem second_exact_value_of_universal
    (huniversal : ∀ D : ConvexDomain, torsionTheory.G D ≤ ENNReal.ofReal
      (2 * secondMoments.stationarity * Real.sqrt secondMoments.area * Real.sqrt D.area)) :
    torsionTheory.cStar = ENNReal.ofReal (spectralConstant secondEigenvalue secondEigenfunction) ∧
    ∃ D : ConvexDomain, D.carrier = normalizedImage secondEigenvalue secondEigenfunction ∧
      D.area = 1 ∧ torsionTheory.G D =
        ENNReal.ofReal (spectralConstant secondEigenvalue secondEigenfunction) :=
  exact_value_of_spectralBridge secondEigenvalue secondEigenfunction
    (secondSpectralBridge_of_universal huniversal)

end Torsion

module

public import Torsion

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The theorem types expose remaining analytic hypotheses. The single
shared dependency traversal below checks all project theorems without
repeatedly traversing the same large mathlib proof dependencies. Explicit
proof parameters are not axioms and must be read in the theorem types. -/

#check Torsion.exact_value_of_spectralBridge
#check Torsion.HilbertDirichlet.exists_dirichletSolution_of_bounded
#check Torsion.ScalingLaw.proved
#check Torsion.markedFluxExistence_proved
#check Torsion.torsionFlux_radial_concaveOn
#check Torsion.Spectral.cauchy_injOn_upperHalfPlane
#check Torsion.Spectral.quadratic_identity_of_holder_boundary_equation
#check Torsion.Spectral.IsRestrictedEigenfunction.eigenvalue_pos
#check Torsion.Spectral.physicalCandidate_isWeakTorsion
#check Torsion.Spectral.cauchyImage_isMarked
#check Torsion.Spectral.torsionFlux_cauchyImage
#check Torsion.Spectral.cauchy_boundary_deriv_holderOn
#check Torsion.Spectral.cauchyAtInfinity_hasDerivAt_zero
#check Torsion.Spectral.IsRestrictedEigenfunction.height_equation
#check Torsion.Spectral.IsRestrictedEigenfunction.height_equation_unique
#check Torsion.Spectral.IsRestrictedEigenfunction.exists_even_or_odd
#check Torsion.Spectral.cauchyBoundaryHomeomorph
#check Torsion.Spectral.frontier_cauchyImage_freeArc_union_segment
#check Torsion.Spectral.gradient_product_physicalCandidate_kernel_boundary_tendsto
#check Torsion.Spectral.IsRestrictedEigenfunction.linear_hilbert_equation
#check Torsion.Spectral.IsRestrictedEigenfunction.cauchy_torsion_construction
#check Torsion.Spectral.IsRestrictedEigenfunction.cauchy_reference_geometry
#check Torsion.Spectral.IsRestrictedEigenfunction.normalized_cauchy_candidate
#check Torsion.Spectral.IsRestrictedEigenfunction.spectralConstant_le_cStar
#check Torsion.Spectral.MemRestrictedFormDomain.fractional_poincare
#check Torsion.Spectral.IsRestrictedEigenfunction.eigenvalue_ge_pi_div_eight
#check Torsion.Spectral.cauchyImage_convex
#check Torsion.Spectral.area_cauchyImage_eq_half_squareMass
#check Torsion.Spectral.cauchyClosureHomeomorph
#check Torsion.Spectral.cauchyJoinedBoundary_regular_frontier_charts
#check Torsion.Spectral.signed_stationarity_physicalCandidate_kernel_tendsto_at_freeArc
#check Torsion.Spectral.radialDomain_cauchyRadialProfile_eq
#check Torsion.Spectral.norm_sq_embed_cauchyRadialProfile
#check Torsion.Spectral.RestrictedHilbert.valueMap_isCompactOperator
#check Torsion.Spectral.exists_first_two_restricted_eigenpairs_even_nonnegative_first
#check Torsion.Spectral.secondEigenfunctionL2_isRestrictedEigenfunction
#check Torsion.Spectral.firstEigenvalue_lt_secondEigenvalue
#check Torsion.Spectral.leastOddEigenvalue_eq_secondEigenvalue
#check Torsion.Spectral.exists_second_odd_nonnegative_simple_restricted_eigenfunction
#check Torsion.Spectral.secondOddEigenfunctionL2_simple
#check Torsion.Spectral.secondOddEigenfunctionL2_pos_ae
#check Torsion.Spectral.MemRestrictedFormDomain.even_mean_zero_energy_ge
#check Torsion.Spectral.oddTrial_memRestrictedFormDomain
#check Torsion.Spectral.oddTrial_energy_lt_even_gap
#check Torsion.Spectral.IsRestrictedEigenfunction.height_equation_of_odd
#check Torsion.Spectral.IsRestrictedEigenfunction.height_Cauchy_boundary_hasDerivAt
#check Torsion.Spectral.IsRestrictedEigenfunction.height_analyticAt_of_odd
#check Torsion.Spectral.exists_second_analytic_simple_restricted_eigenfunction
#check Torsion.Spectral.secondEigenfunction_isRestrictedEigenfunction
#check Torsion.Spectral.secondEigenfunction_analyticOnNhd
#check Torsion.Spectral.secondEigenfunction_simple
#check Torsion.Spectral.secondEigenvalue_le_of_isRestrictedEigenfunction_ne_first
#check Torsion.Spectral.IsRestrictedEigenfunction.regularEigenfunction_pos
#check Torsion.Spectral.secondEigenfunction_pos
#check Torsion.Spectral.exists_second_positive_analytic_simple_restricted_eigenfunction
#check Torsion.Spectral.semicircleBarrier_memRestrictedFormDomain
#check Torsion.Spectral.semicircleBarrier_weak_equation
#check Torsion.Spectral.secondEigenfunction_sqrt_boundary_bound
#check Torsion.Spectral.secondEigenfunction_exteriorResidualZero_integrable
#check Torsion.Spectral.secondEigenfunction_global_schwartz_equation
#check Torsion.Spectral.secondEigenfunction_second_deriv_eq
#check Torsion.Spectral.secondEigenfunction_strictConcaveOn
#check Torsion.Spectral.secondEigenfunction_concaveOn
#check Torsion.Spectral.secondEigenfunction_holder_half
#check Torsion.Spectral.secondEigenfunction_linear_hilbert_equation
#check Torsion.Spectral.exists_second_restricted_spectral_profile
#check Torsion.Spectral.secondMoments
#check Torsion.Spectral.secondCauchyDomain_isWeakTorsion
#check Torsion.Spectral.secondCauchyDomain_area
#check Torsion.Spectral.secondCauchyDomain_flux
#check Torsion.Spectral.secondCalibrationDensity_euler
#check Torsion.Spectral.secondCalibrationDensity_constant
#check Torsion.Spectral.second_spectralConstant_le_cStar
#check Torsion.Spectral.second_radial_bound_of_smooth_local_derivative
#check Torsion.secondSpectralBridge_of_universal
#check Torsion.second_exact_value_of_universal
#check Torsion.RadialCalibration.calibration_of_smooth_local_derivative
#check Torsion.HalfPlane.integral_poisson
#check Torsion.HalfPlane.fundamental_circle_flux
#check Torsion.HalfPlane.green_hasDerivAt_boundary_source
#check Torsion.Spectral.physicalGreen_regular_part_tendsto
#check Torsion.Spectral.physicalGreen_marked_source_quotient_tendsto
#check Torsion.DirichletTheory.G_area_bound_of_exhaustion
#check Torsion.IsWeakTorsion.tendsto_eLpNorm_gradient_of_outer_dilation
#check Torsion.DirichletTheory.G_area_bound_of_metric_outer
#check Torsion.HalfPlane.fundamental_weak_source
#check Torsion.DirichletTheory.G_translate
#check Torsion.DirichletTheory.tendsto_gradient_of_outer_approximation
#check Torsion.ConvexDomain.area_tendsto_of_outer_approximation
#check Torsion.DirichletTheory.G_area_bound_of_outer_approximation
#check Torsion.HalfPlane.fundamental_weak_source_at
#check Torsion.DirichletTheory.tendsto_of_outer_approximation
#check Torsion.HalfPlane.green_pairing_integrable
#check Torsion.HalfPlane.green_weak_source
#check Torsion.Spectral.physicalGreen_weak_source
#check Torsion.Spectral.physicalGreen_pairing_integrable
#check Torsion.Spectral.physicalGreenRegular_contDiffOn
#check Torsion.Spectral.physicalGreen_marked_normal_source_hasDerivWithinAt
#check Torsion.Spectral.physicalMarkedPoisson_eq_kernel
#check Torsion.Spectral.second_signed_poisson_stationarity
#check Torsion.Spectral.physicalHarmonicLift_marked_normal_tendsto
#check Torsion.Spectral.physicalHarmonicLift_marked_boundary_tendsto
#check Torsion.ConvexDomain.exists_smooth_strictConvex_outer_sequence
#check Torsion.DirichletTheory.G_area_bound_of_smooth_strictConvex
#check Torsion.secondSpectralBridge_of_smooth_comparison
#check Torsion.Shape.exists_MemH10_transport_deformation
#check Torsion.Shape.exists_weakTorsion_pullback_deformation
#check Torsion.Shape.realMatrix_pullbackEnergyOperator_deformation
#check Torsion.Shape.physical_forcing_hasDerivAt_zero
#check Torsion.Shape.uniformEnergyCoefficient_hasDerivAt_zero
#check Torsion.Shape.uniformEnergyCoefficient_eventually_apply
#check Torsion.IsWeakTorsion.le_slab_barrier
#check Torsion.Spectral.physicalGreen_boundary_tendsto
#check Torsion.Shape.exists_local_radial_deformation
#check Torsion.Shape.materialSolution_hasDerivAt_zero
#check Torsion.Shape.materialDerivative_compact_test_equation
#check Torsion.Shape.exists_torsionFlux_deformation_hasDerivAt
#check Torsion.Shape.exists_local_radialFlux_hasDerivAt
#check Torsion.Spectral.shapeCorrection_memH10
#check Torsion.Spectral.torsionFlux_cauchy_deformation_hasDerivAt
#check Torsion.Spectral.torsionFlux_cauchy_boundary_hadamard
#check Torsion.Spectral.cauchy_radial_torsionFlux_hasDerivAt
#check Torsion.Spectral.second_localized_hadamard
#check Torsion.Spectral.second_radial_calibration
#check Torsion.Spectral.second_radial_bound
#check Torsion.ConvexDomain.exists_nearest_supported_frontier
#check Torsion.ConvexDomain.exists_marked_flat_outer
#check Torsion.DirichletTheory.G_isometryPreimage
#check Torsion.IsWeakTorsion.exists_continuous_smooth_representative
#check Torsion.IsWeakTorsion.lipschitzWith_of_boundary_collar_approx
#check Torsion.IsWeakTorsion.gradient_bound_of_boundary_collar_approx
#check Torsion.HasMarkedFlux.le_second_spectral_bound
#check Torsion.exists_uniform_slab_marked_torsion_normal_quotient_constant_on_representative
#check Torsion.exists_uniform_second_supported_normal_bound
#check Torsion.IsWeakTorsion.second_boundary_collar
#check Torsion.DirichletTheory.G_le_second_spectral_bound
#check Torsion.second_universal
#check Torsion.secondReferenceCertificate
#check Torsion.secondSpectralBridge
#check Torsion.second_exact_value
#print Torsion.ReferenceCertificate
#print Torsion.SpectralBridge


/- Check every theorem defined by a project module, including generated
theorems and backports in existing library namespaces, and reject admissions
or any nonstandard axiom dependency. -/
run_cmd do
  let env ← Lean.getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    let inProjectModule := match env.getModuleIdxFor? name with
      | some idx => (`Torsion).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if ((`Torsion).isPrefixOf name || inProjectModule) && info.isTheorem then some name else none
  -- Lean now records axiom dependencies in imported module metadata.
  -- Use its public collector rather than the former internal traversal API.
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless [(`propext), (`Classical.choice), (`Quot.sound)].contains ax do
        throwError "Unexpected axiom {ax} in dependencies of {name}"
  Lean.logInfo m!"Audited {names.length} project theorems: only propext, Classical.choice, Quot.sound allowed."

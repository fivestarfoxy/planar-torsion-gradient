module

import all Torsion
-- Load every project proof body, including private and generated declarations.
import all Torsion.BoundaryLowerBound
import all Torsion.BoundedDomains
import all Torsion.Calibration
import all Torsion.CauchyConformalGeometry.BoundaryCurvature
import all Torsion.CauchyConformalGeometry.BoundaryDerivative
import all Torsion.CauchyConformalGeometry.BoundaryGeometry
import all Torsion.CauchyConformalGeometry.ImageSeparation
import all Torsion.CauchyConformalGeometry.Inverse
import all Torsion.CauchyConformalGeometry.Univalence
import all Torsion.CauchyConformalGeometry
import all Torsion.CauchyQuadraticIdentity
import all Torsion.CauchySpectralIdentity
import all Torsion.CauchyTransform
import all Torsion.CauchyTransformBoundaryDerivative
import all Torsion.CauchyTransformBoundaryExtension
import all Torsion.CauchyTransformDecay
import all Torsion.CauchyTransformHeightDerivative
import all Torsion.CauchyTransformImageBound
import all Torsion.CauchyTransformImageFrontier
import all Torsion.CauchyTransformImaginaryBoundary
import all Torsion.CauchyTransformIntegrationByParts
import all Torsion.CauchyTransformMoments
import all Torsion.CauchyTransformPoisson
import all Torsion.CauchyTransformRealBoundary
import all Torsion.CauchyTransformUniqueness
import all Torsion.ClassicalWeakTorsion
import all Torsion.Comparison
import all Torsion.ComplexIdentity
import all Torsion.ContinuousProfiles
import all Torsion.Curvature
import all Torsion.CurvatureFromConcavity
import all Torsion.Definitions
import all Torsion.Dilation
import all Torsion.DilationSobolev
import all Torsion.DilationWeak
import all Torsion.DirichletExhaustion
import all Torsion.DirichletGalerkin
import all Torsion.DomainComparison
import all Torsion.Hessian
import all Torsion.HilbertDirichlet
import all Torsion.L2Dominated
import all Torsion.Main
import all Torsion.MarkedBoundaryRegularity
import all Torsion.MarkedFlux
import all Torsion.MarkedFluxComparison
import all Torsion.MarkedFluxExhaustion
import all Torsion.MarkedFluxLowerBound
import all Torsion.Moments
import all Torsion.PhysicalCauchyBoundary
import all Torsion.PhysicalCauchyPositivity
import all Torsion.PhysicalCauchySobolev
import all Torsion.PhysicalCauchyTorsion
import all Torsion.PhysicalCauchyWeakTorsion
import all Torsion.PhysicalCauchyZeroExtension
import all Torsion.PhysicalTorsionCalculus
import all Torsion.Poincare
import all Torsion.ProvedMain
import all Torsion.RadialConcavity.Mollification
import all Torsion.RadialConcavity
import all Torsion.RadialFluxConcavity.Transfer
import all Torsion.RadialFluxConcavity
import all Torsion.RadialGeometry
import all Torsion.RadialStability
import all Torsion.RestrictedSpectralDistribution
import all Torsion.RestrictedSpectralForm.Algebra
import all Torsion.RestrictedSpectralForm
import all Torsion.SmoothPositivePart
import all Torsion.Sobolev
import all Torsion.SobolevAdd
import all Torsion.SobolevBoundaryAdmission
import all Torsion.SobolevComposition
import all Torsion.SobolevCore
import all Torsion.SobolevCutoff
import all Torsion.SobolevEnergy
import all Torsion.SobolevExhaustion
import all Torsion.SobolevGraph
import all Torsion.SobolevIdeal
import all Torsion.SobolevIntersection
import all Torsion.SobolevLattice
import all Torsion.SobolevLatticeContinuity
import all Torsion.SobolevLocalization
import all Torsion.SobolevMinContinuity
import all Torsion.SobolevMonotone
import all Torsion.SobolevPositivePart
import all Torsion.SobolevScalar
import all Torsion.SobolevSupport
import all Torsion.SobolevUniqueness
import all Torsion.SpectralBoundaryZeros
import all Torsion.SpectralDefinitions
import all Torsion.SpectralHolderCalculus
import all Torsion.SpectralMain
import all Torsion.SpectralMomentIdentity
import all Torsion.SpectralNormalization
import all Torsion.SpectralPositivity
import all Torsion.SpectralScaling
import all Torsion.Stability
import all Torsion.TorsionPositivity
import all Torsion.WeakGradient
import all Torsion.WeakHarmonicRegularity
import all Torsion.WeakHarmonicWeyl.Associativity
import all Torsion.WeakHarmonicWeyl.Classical
import all Torsion.WeakHarmonicWeyl.ConvolutionEstimates
import all Torsion.WeakHarmonicWeyl.MeanValue
import all Torsion.WeakHarmonicWeyl.RadialKernel
import all Torsion.WeakHarmonicWeyl.Representative
import all Torsion.WeakHarmonicWeyl.RepresentativeGradient
import all Torsion.WeakHarmonicWeyl
import all Torsion.WeakReflection.Admission
import all Torsion.WeakReflection.Odd
import all Torsion.WeakReflection.Poisson
import all Torsion.WeakReflection.Tests
import all Torsion.WeakReflection.Translation
import all Torsion.WeakReflection.ZeroGradient
import all Torsion.WeakReflection
import all Torsion.CauchyConformalGeometry.BoundaryHolder
import all Torsion.CauchyConformalGeometry.CompactifiedBoundary
import all Torsion.CauchyConformalGeometry.ExteriorBoundary
import all Torsion.CauchyConformalGeometry.FlatSegment
import all Torsion.CauchyConformalGeometry.Infinity
import all Torsion.CauchyConformalGeometry.MarkedGeometry
import all Torsion.CauchyTransformExterior
import all Torsion.PhysicalCauchyKernel
import all Torsion.PhysicalCauchyMarkedFlux
import all Torsion.RestrictedSpectralCorePrimitive
import all Torsion.RestrictedSpectralIntegrated
import all Torsion.RestrictedSpectralPrimitive
import all Torsion.RestrictedSpectralSymmetry
import all Torsion.CauchyBoundaryStationarity
import all Torsion.CauchyConformalGeometry.BoundaryJunctionCoverage
import all Torsion.CauchyConformalGeometry.BoundaryJunctionGeometry
import all Torsion.CauchyConformalGeometry.BoundaryJunctionHolder
import all Torsion.CauchyConformalGeometry.CompactifiedClosure
import all Torsion.CauchyConformalGeometry.Convexity
import all Torsion.CauchyConformalGeometry.ConvexityCriterion
import all Torsion.CauchyConformalGeometry.ConvexityNormals
import all Torsion.CauchyConformalGeometry.ConvexitySlope
import all Torsion.CauchyConformalGeometry.ConvexitySupport
import all Torsion.CauchyConformalGeometry.InverseBoundary
import all Torsion.CauchyImageArea
import all Torsion.CauchyImageAreaBottom
import all Torsion.CauchyImageAreaBoundary
import all Torsion.CauchyImageAreaDecay
import all Torsion.CauchyImageAreaExact
import all Torsion.CauchyImageAreaExhaustion
import all Torsion.CauchyRadialDomain
import all Torsion.CauchyRadialGeometry
import all Torsion.CauchyRadialProfile
import all Torsion.CauchyTracePairingLimit
import all Torsion.FourierHilbertHeight
import all Torsion.FourierHilbertKernel
import all Torsion.FourierHilbertPairing
import all Torsion.FourierPlancherel
import all Torsion.RestrictedSpectralEnergyContinuity
import all Torsion.RestrictedSpectralHilbert
import all Torsion.RestrictedSpectralPoincare
import all Torsion.SpectralCandidate
import all Torsion.CompactSpectral.PositiveEigenpair
import all Torsion.CompactSpectral.RayleighCompact
import all Torsion.CompactSpectral.SecondAfterFirst
import all Torsion.CompactSpectral.TwoEigenpairs
import all Torsion.CompactSpectral.WeakHilbertCompact
import all Torsion.CompactSpectral
import all Torsion.ComplexAxisRemovability
import all Torsion.ComplexConjugateDerivative
import all Torsion.ComplexODEContinuation
import all Torsion.ComplexPrimitives
import all Torsion.ComplexSchwarzReflection
import all Torsion.ComplexSchwarzReflectionBasic
import all Torsion.ComplexUpperPrimitive
import all Torsion.FourierParsevalApproximation
import all Torsion.RestrictedSpectralAnalyticHeight
import all Torsion.RestrictedSpectralBoundaryPrimitive
import all Torsion.RestrictedSpectralBoundaryRegularity
import all Torsion.RestrictedSpectralCompactness
import all Torsion.RestrictedSpectralCoreDirections
import all Torsion.RestrictedSpectralCosineVariance
import all Torsion.RestrictedSpectralEigenpairs
import all Torsion.RestrictedSpectralEvenFourierBounds
import all Torsion.RestrictedSpectralEvenGap
import all Torsion.RestrictedSpectralFourierBounds
import all Torsion.RestrictedSpectralFourierContinuity
import all Torsion.RestrictedSpectralFourierWindows
import all Torsion.RestrictedSpectralGagliardo
import all Torsion.RestrictedSpectralGagliardoDomain
import all Torsion.RestrictedSpectralGagliardoKernel
import all Torsion.RestrictedSpectralGagliardoSymbol
import all Torsion.RestrictedSpectralGraph
import all Torsion.RestrictedSpectralGraphHilbert
import all Torsion.RestrictedSpectralGroundSign
import all Torsion.RestrictedSpectralGroundState
import all Torsion.RestrictedSpectralHeightParity
import all Torsion.RestrictedSpectralHeightRegularity
import all Torsion.RestrictedSpectralInterpolation
import all Torsion.RestrictedSpectralIntervalHolder
import all Torsion.RestrictedSpectralLattice
import all Torsion.RestrictedSpectralLatticeApprox
import all Torsion.RestrictedSpectralMinMax
import all Torsion.RestrictedSpectralMinimizer
import all Torsion.RestrictedSpectralOddCore
import all Torsion.RestrictedSpectralOddEigenpair
import all Torsion.RestrictedSpectralOddFold
import all Torsion.RestrictedSpectralOddFoldApproximation
import all Torsion.RestrictedSpectralOddFoldCore
import all Torsion.RestrictedSpectralOddGagliardo
import all Torsion.RestrictedSpectralOddGap
import all Torsion.RestrictedSpectralOddGapBounds
import all Torsion.RestrictedSpectralOddGroundSign
import all Torsion.RestrictedSpectralOddGroundState
import all Torsion.RestrictedSpectralOddLattice
import all Torsion.RestrictedSpectralOddMinimizer
import all Torsion.RestrictedSpectralOddPositivity
import all Torsion.RestrictedSpectralOddSelection
import all Torsion.RestrictedSpectralOddStrictMarkov
import all Torsion.RestrictedSpectralPairingContinuity
import all Torsion.RestrictedSpectralParseval
import all Torsion.RestrictedSpectralPolynomialTrial
import all Torsion.RestrictedSpectralPolynomialTrialApprox
import all Torsion.RestrictedSpectralPositiveSets
import all Torsion.RestrictedSpectralPositiveTest
import all Torsion.RestrictedSpectralPositivity
import all Torsion.RestrictedSpectralReflectionOperator
import all Torsion.RestrictedSpectralRegularRepresentative
import all Torsion.RestrictedSpectralResolvent
import all Torsion.RestrictedSpectralSecondEigenpair
import all Torsion.RestrictedSpectralSecondIdentification
import all Torsion.RestrictedSpectralSecondParity
import all Torsion.RestrictedSpectralSelection
import all Torsion.RestrictedSpectralStrictMarkov
import all Torsion.RestrictedSpectralTranslation
import all Torsion.RestrictedSpectralWeakClosure
import all Torsion.RestrictedSpectralWeakIntegrated
import all Torsion.RestrictedSpectralWeakPrimitive
import all Torsion.TrigonometricQuadraticBound
import all Torsion.RestrictedSpectralSecondProfile
import all Torsion.RestrictedSpectralCauchyL1
import all Torsion.RestrictedSpectralCauchyMinimum
import all Torsion.RestrictedSpectralCauchySecondDerivative
import all Torsion.RestrictedSpectralOddKernelMinimum
import all Torsion.RestrictedSpectralQuadraticZero
import all Torsion.RestrictedSpectralSignRegularity
import all Torsion.RestrictedSpectralStrongMaximum
import all Torsion.RestrictedSpectralWeakCauchy
import all Torsion.RestrictedSpectralBarrierComparison
import all Torsion.RestrictedSpectralCompactSmoothInterpolation
import all Torsion.RestrictedSpectralComposition
import all Torsion.RestrictedSpectralConcaveHolder
import all Torsion.RestrictedSpectralConcavity
import all Torsion.RestrictedSpectralConcavityBounds
import all Torsion.RestrictedSpectralConcavityComposition
import all Torsion.RestrictedSpectralConcavitySign
import all Torsion.RestrictedSpectralEndpointComparison
import all Torsion.RestrictedSpectralEndpointCutoffBasic
import all Torsion.RestrictedSpectralEndpointCutoffs
import all Torsion.RestrictedSpectralEndpointIntegrability
import all Torsion.RestrictedSpectralExteriorEnergy
import all Torsion.RestrictedSpectralExteriorIntegrability
import all Torsion.RestrictedSpectralExteriorKernel
import all Torsion.RestrictedSpectralExteriorKernelIntegral
import all Torsion.RestrictedSpectralExteriorTest
import all Torsion.RestrictedSpectralFourierIdentification
import all Torsion.RestrictedSpectralGagliardoAdmission
import all Torsion.RestrictedSpectralGlobalEquation
import all Torsion.RestrictedSpectralSchwartz
import all Torsion.RestrictedSpectralSchwartzFourier
import all Torsion.RestrictedSpectralSecondConcavity
import all Torsion.RestrictedSpectralSecondEndpoint
import all Torsion.RestrictedSpectralSecondEndpointIntegrability
import all Torsion.RestrictedSpectralSecondExteriorIntegrability
import all Torsion.RestrictedSpectralSecondHolder
import all Torsion.RestrictedSpectralSemicircle
import all Torsion.RestrictedSpectralSemicircleAdmission
import all Torsion.RestrictedSpectralSemicircleComplex
import all Torsion.RestrictedSpectralSemicircleKernel
import all Torsion.RestrictedSpectralSemicircleWeak
import all Torsion.RestrictedSpectralSemicircleWeight
import all Torsion.RestrictedSpectralSmallSupport
import all Torsion.RestrictedSpectralTestPartition
import all Torsion.RestrictedSpectralWeakEnergyLimit
import all Torsion.CanonicalRadialCalibration
import all Torsion.CanonicalSpectralCandidate
import all Torsion.ConvexOuterDilation
import all Torsion.GradientBoundExhaustion
import all Torsion.HalfPlaneGreen
import all Torsion.HalfPlaneGreenInfinity
import all Torsion.HalfPlaneGreenSource
import all Torsion.HalfPlanePoisson
import all Torsion.OuterDomainConvergence
import all Torsion.OuterGradientBounds
import all Torsion.PhysicalCauchyGreen
import all Torsion.RadialCalibrationCutoff
import all Torsion.RadialCalibrationSmooth
import all Torsion.SmoothCompactApproximation
import all Torsion.ConvexOuterApproximation
import all Torsion.HalfPlaneGreenSourceTranslation
import all Torsion.TorsionTranslation
import all Torsion.PolarIntegrability
import all Torsion.CanonicalSmoothReduction
import all Torsion.ClassicalWeakLaplacian
import all Torsion.ConformalGreenRegularPart
import all Torsion.ConvexMollification
import all Torsion.GreenRegularPart
import all Torsion.PhysicalCauchyGreenNormal
import all Torsion.PhysicalCauchyGreenWeak
import all Torsion.PhysicalCauchyHarmonicBoundary
import all Torsion.PhysicalCauchyHarmonicLift
import all Torsion.PhysicalCauchyHarmonicMarked
import all Torsion.PhysicalCauchyPoisson
import all Torsion.PositiveLocalInverse
import all Torsion.ShapeChangeOfVariables
import all Torsion.ShapeCoefficients
import all Torsion.ShapeDeformation
import all Torsion.ShapeEnergyOperatorMatrix
import all Torsion.ShapeForcing
import all Torsion.ShapeGradient
import all Torsion.ShapeSobolevDeformation
import all Torsion.ShapeSobolevTransport
import all Torsion.ShapeUniformCoefficients
import all Torsion.ShapeWeakPullback
import all Torsion.SlabTorsionBarrier
import all Torsion.SmoothConvexLevelSets
import all Torsion.SmoothConvexOuterApproximation
import all Torsion.SmoothConvexReduction
import all Torsion.PhysicalCauchyGreenBoundary
import all Torsion.CanonicalHadamard
import all Torsion.CanonicalRadialStability
import all Torsion.CanonicalGradientStability
import all Torsion.RadialSymmetricDifference
import all Torsion.CauchyConvectionLp
import all Torsion.CauchyFreeArcGradient
import all Torsion.CauchyFreeArcInverse
import all Torsion.CauchyRadialHadamard
import all Torsion.CauchyRadialHadamardDensity
import all Torsion.CauchyShapeBoundaryData
import all Torsion.CauchyShapeBoundaryTrace
import all Torsion.CauchyShapeCorrection
import all Torsion.CauchyShapeHadamard
import all Torsion.CompactLocalBounds
import all Torsion.FixedKernelContinuity
import all Torsion.HarmonicBoundaryUniqueness
import all Torsion.LpParameterDerivative
import all Torsion.MarkedFluxDifferentiation
import all Torsion.MarkedFluxFixedKernel
import all Torsion.PhysicalCauchyHarmonicBound
import all Torsion.PhysicalCauchyHarmonicClosure
import all Torsion.PhysicalCauchyHarmonicDerivative
import all Torsion.PhysicalCauchyHarmonicLp
import all Torsion.PhysicalCauchyHarmonicWeak
import all Torsion.RadialDeformation
import all Torsion.RadialDeformationCollar
import all Torsion.RadialDeformationField
import all Torsion.RadialDeformationImage
import all Torsion.ShapeCauchyEulerian
import all Torsion.ShapeCoefficientForms
import all Torsion.ShapeEulerianCommutator
import all Torsion.ShapeMarkedFluxDerivative
import all Torsion.ShapeMarkedPatch
import all Torsion.ShapeMaterialBase
import all Torsion.ShapeMaterialEulerian
import all Torsion.ShapeMaterialIdentification
import all Torsion.ShapeMaterialInverse
import all Torsion.ShapeMaterialSolution
import all Torsion.SignedBoundaryAdmission
import all Torsion.SmoothZeroLevel
import all Torsion.WeakDirichletGradientUniqueness
import all Torsion.ZeroBoundaryContinuity
import all Torsion.ShapeCoefficientOperators
import all Torsion.ShapeCoefficientScalar
import all Torsion.ShapeMaterialGeneric
import all Torsion.CauchyHadamardBoundaryIntegral
import all Torsion.BoundaryCollarGradient
import all Torsion.CanonicalOptimization
import all Torsion.CanonicalSupportingFlux
import all Torsion.CanonicalUniversal
import all Torsion.ConvexGaugeRadial
import all Torsion.ConvexSupportingPoint
import all Torsion.ConvexSupportingRadial
import all Torsion.ConvexTorsionContinuity
import all Torsion.ConvolutionDerivativeBounds
import all Torsion.FlatOuterHullArea
import all Torsion.HarmonicNormalTaylor
import all Torsion.LocalHarmonicBound
import all Torsion.MarkedHullCollarComparison
import all Torsion.MarkedTorsionTaylor
import all Torsion.NormalFrame
import all Torsion.NormalFrameFlatPatch
import all Torsion.RealTaylorBound
import all Torsion.SobolevIsometry
import all Torsion.SupportedConvexFlatHull
import all Torsion.SupportedConvexFlatHullUniform
import all Torsion.SupportingSublevelRay
import all Torsion.TorsionIsometry
import all Torsion.UniformSupportedCollar
import all Torsion.WeakTorsionInterior
import all Torsion.WeakTorsionRepresentative
import all Torsion.WeakTranslationLipschitz

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
#check Torsion.Spectral.second_radial_normalized_deficit
#check Torsion.Spectral.second_radial_rigidity
#check Torsion.Spectral.second_radial_area_one_deficit
#check Torsion.Spectral.second_radial_area_one_equality_iff
#check Torsion.Spectral.second_marked_area_one_symmDiff_deficit
#check Torsion.Spectral.second_marked_area_one_domain_rigidity
#check Torsion.DirichletTheory.exists_supporting_flatHull_flux_gt
#check Torsion.DirichletTheory.exists_supporting_positive_radial_flux_gt
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


/- Check every declaration defined by a project module, including data
definitions, unused axioms, generated declarations, and backports in library
namespaces. This also catches admissions outside theorem bodies. -/
run_cmd do
  -- Enumerate the complete checked environment, including declarations
  -- hidden from the current public export scope of the module system.
  let env := (← Lean.getEnv).setExporting false
  let mut projectModuleCount : Nat := 0
  for imported in env.header.modules do
    if imported.module == `Challenge then
      throwError "Reference Challenge module must not enter the proof audit"
    if (`Torsion).isPrefixOf imported.module then
      projectModuleCount := projectModuleCount + 1
      unless imported.importAll do
        throwError "Incomplete audit: {imported.module} must be imported with import all"
  let declarations := env.constants.toList.filterMap fun (name, info) =>
    let inProjectModule := match env.getModuleIdxFor? name with
      | some idx => (`Torsion).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if (`Torsion).isPrefixOf name || inProjectModule then some (name, info.isTheorem) else none
  let names := declarations.filterMap fun (name, isTheorem) =>
    if isTheorem then some name else none
  -- Lean now records axiom dependencies in imported module metadata.
  -- Use its public collector rather than the former internal traversal API.
  for (name, _) in declarations do
    for ax in (← Lean.collectAxioms name) do
      unless [(`propext), (`Classical.choice), (`Quot.sound)].contains ax do
        throwError "Unexpected axiom {ax} in dependencies of {name}"
  unless !names.isEmpty do
    throwError "Incomplete audit: no project theorem roots found"
  Lean.logInfo m!"Checked full imports for {projectModuleCount} project modules."
  Lean.logInfo m!"Audited {declarations.length} project declarations ({names.length} theorems): only propext, Classical.choice, Quot.sound allowed."

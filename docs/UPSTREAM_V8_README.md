# Planar torsion-gradient optimization in Lean

**Status: the exact optimal constant and attainment by the constructed second
spectral Cauchy image are now proved unconditionally.**

`Torsion.second_exact_value` has no spectral, geometric, shape-variation or
comparison arguments. The original `ReferenceCertificate` and `SpectralBridge`
interfaces now have actual constructed instances, `secondReferenceCertificate`
and `secondSpectralBridge`. In particular `second_universal` proves the original
universal calibrated upper bound for **every original `ConvexDomain`**, using
the actual weak-gradient essential supremum. No admissible class, optimization
constant or concrete definition was changed.

The constructed canonical second restricted half-Laplacian eigenfunction is
normalized, odd, zero outside the interval, interior analytic, strictly positive
on `(0,1)`, strictly concave on `[0,1]`, and globally one-half Hölder. Its pointwise
linear Hilbert equation follows from its original weak Fourier equation. These
proved facts supply the Cauchy construction, convexity, exact Euclidean area,
actual weak torsion and marked flux. Correctly normalized physical weak Green
and Poisson kernels, signed stationarity and the localized Hadamard formula on
the actual spectral reference supply the unconditional sharp radial bound.

The final comparison uses actual positive gauge radial outer domains, nearest
supporting points and physical orthogonal covariance. Adding a small horizontal
base constructs marked convex outer hulls. A fixed interior ball gives uniform
flat patches and an explicit area loss. Caccioppoli and fixed reflection kernels
give a uniform genuine torsion Taylor estimate on those patches. First choosing
the hull radius, then the boundary distance, gives approximate sharp distance
collars. An actual compact-test maximum principle and weak translation comparison
remove the collar losses and give the exact global Lipschitz constant. Local
Weyl regularity identifies this derivative with the original weak gradient.
This proves the universal inequality directly for arbitrary bounded open convex
domains, without assuming smooth boundary torsion regularity or a boundary
maximum-gradient theorem. The previously proved smooth outer approximations and
limit theorems are preserved.

All earlier mathematical source modules are retained byte-for-byte. General
conditional theorems remain available as reusable interfaces; their parameters
are now discharged for the canonical second spectral construction.

Continuation source: Caden Young, *An exact spectral construction for the optimal
planar torsion gradient*, 13 October 2026, audit revision, attached as
`torsion_exact_spectral_construction-1.pdf`. Earlier PDE/calibration lemma
numbering is retained from the original development. The floating-point
illustrations are not inputs to any proof.

## Build and audit

Lean **4.19.0** and mathlib **v4.19.0**, commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Exact dependency revisions are
recorded in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

`Torsion.lean` imports the entire development. `Audit.lean` displays the
general interface types, the unconditional final theorem, and checks every theorem declared in a project
module, including generated declarations and backports in existing library
namespaces, rejecting dependencies beyond
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom
axiom, or unproved theorem instance is used. Explicit proof parameters are
not reported as axioms: read the theorem types as well as the audit.
`validation.txt` records the final build and audit results. The continuation
contains **392 source modules / 52,713 lines**, with **3,587 project theorem
declarations audited** (including backports in existing library namespaces).
All original source modules are retained; no toolchain or dependency revision
was changed.

## Proved development

| Block | Actual proved result |
| --- | --- |
| H¹₀ graph closure | Zero, sum, scalar, negative and difference closure; compact-core integrability; equivalence with a closed submodule of the actual L² value/gradient product. |
| Poincaré | A finite positive constant for every bounded planar set, obtained from the two-dimensional Gagliardo–Nirenberg–Sobolev inequality, Hölder and the defining closure. No boundary regularity or convexity is assumed. |
| Weak existence | Actual `DirichletSolution` on every bounded measurable set, including empty and nonconvex domains, constructed using the closed graph and Lax–Milgram. `HilbertDirichlet.dirichletTheory` inhabits the previously hypothetical theory. |
| Weak uniqueness | Global a.e. uniqueness of the value and gradient; essential gradient norms and the area-one supremum are independent of solution choices. |
| Distributional gradient | Actual integration by parts for the graph closure and uniqueness of arbitrary weak gradients from the a.e. value class. |
| Sobolev lattice calculus | Smooth Lipschitz composition, flat smooth positive-part approximation, actual positive/negative/min/max graph formulas, zero-level gradient vanishing, and strong H¹ lattice continuity. |
| Weak torsion positivity | Actual negative-part testing proves the weak torsion solution is nonnegative a.e. on every bounded set. |
| Lemma 3.2 and localization | Smooth cutoffs localize compact a.e. support while preserving the original domain; the actual Sobolev ideal and intersection-admissibility theorems are proved for arbitrary open sets, including slits. |
| Lemma 3.3, torsion | Actual domain monotonicity and torsion supermodularity follow from the genuine weak equations. No admissible-test or truncation-energy assumptions remain. |
| Increasing domains | Eventual compact-test admission, closed-graph density, actual Galerkin orthogonality and Céa bounds, and strong global L² convergence of values and gradients. Fixed-kernel local regularity and odd reflection also prove convergence of the actual marked flux (Lemma 3.7), with no derivative-convergence assumption. |
| Physical scaling | Actual domain dilation, Euclidean area scaling, measure/integral change of variables, smooth and weak gradient scaling, H¹₀ transport, weak PDE transport, and `ScalingLaw.proved`. |
| Lemma 3.4 | Fully proved from exactly continuity, degree-one positive homogeneity and lattice supermodularity on the finite positive orthant. Includes Euler differentiation, off-diagonal signs, Hessian symmetry, log-coordinate mollification, preservation and convergence. |
| Radial geometry | Actual radial domains are open, bounded and marked. Polar coordinates and Tonelli prove their Euclidean area equals the stated angular integral. |
| Local Weyl and flat reflection | Caccioppoli estimates, actual radial harmonic reproduction, fixed smooth local value and gradient representatives, actual upper-half Sobolev admission, cross-axis odd reflection, and the quadratic torsion correction. |
| Constructed marked flux | Every actual marked weak torsion problem has a finite inward flux, independent of representatives. Comparison, physical scaling and supermodularity are proved from the genuine weak PDE, as is Q(D) ≤ the actual interior essential gradient norm. |
| Theorem 3.6 | Actual interface-correct step domains, their lattice/scale geometry, finite-dimensional concavity and compact-cover approximation prove concavity of the actual constructed torsion flux on positive continuous profiles. No flux-law or boundary-regularity hypotheses remain. |
| Continuous profiles | Actual L² embedding of C([0,π]), endpoint-inclusive injectivity, squared-norm and geometric-area identities, and the continuous-profile versions of deficit and rigidity. |
| Cauchy interior analysis | Actual holomorphy, differentiation under the integral, analyticity, quantitative decay and infinity moments for F, A and their derivatives. |
| Integrated eigenfunction profile | Actual global Y′ = −φ, C¹ regularity, compact support, integrability and transfer of Hölder derivative estimates from the stated continuous odd zero-exterior input. |
| Actual boundary traces | Absolutely convergent subtracted real Hilbert trace, integrable Hölder majorants, joint real continuity, a fixed-kernel Poisson extension and joint imaginary continuity. These construct genuine complex extensions of F, A, F′, A′ to the entire closed half-plane and arbitrary-approach limits, including the support endpoints. |
| Holomorphic uniqueness | A bounded holomorphic function continuous on the closed half-plane and real on its boundary is constant; an interior decay sequence forces zero. The proof uses Phragmén–Lindelöf and maximum modulus. |
| Quadratic identity and moments | The explicit linear Hilbert equation plus Hölder spectral data now imply the actual holomorphic quadratic identity, aN = 2bM, positive b and a unique velocity zero. All required extensions, bounds, holomorphy and decay are proved; the nonlinear identity is no longer assumed in this derivation. |
| Curvature estimate | The genuine concavity tangent inequalities, primitive estimates and the proved velocity ODE yield strict positivity of the actual curvature numerator on the positive half of the free arc from the linear Hilbert equation. |
| Interior conformal geometry | Pairing the actual Cauchy integrals proves derivative nonvanishing, real-image separation and full injectivity in H. The actual image is open and bounded, with a constructed analytic inverse and homeomorphism from H. No Jordan or univalence input is assumed. |
| Boundary geometry | Actual C¹ boundary parametrization, embedded free arc, positive real exterior tangents and injectivity on the entire real line. The one-point compactified real boundary is homeomorphic to the actual image frontier, which is exactly the free arc plus the nondegenerate flat segment. The actual Cauchy image is marked, including a proved upper half-ball near zero. The entire compactified closed half-plane is homeomorphic to the actual closed image. The infinity coordinate is analytic with derivative M/π. From the proved linear Hilbert equation, the actual tangent is Hölder on the closed free arc; integrating the profile estimate proves the height endpoint vanishing bound of order 1+α. |
| Convexity | Actual tangent support inequalities follow from the proved curvature and velocity/profile ratio monotonicity. Supporting functionals on the actual frontier imply convexity of the actual image. `cauchyConvexDomain` is an existing `ConvexDomain` record constructed by these proofs, rather than an assumed certificate. |
| Exact geometric area | The actual Euclidean measure is the half-plane Jacobian integral `∫ |F′|²`. The actual area field, mathlib's rectangular Green identity, proved outer-boundary decay and increasing rectangle exhaustion give `|F(H)| = aN - bM = bM = aN/2`. This is not a definition by signed area. |
| Physical junction charts | Actual embedded regular C¹,α charts parametrize relative neighborhoods of both joins. A clamped tangent produces the true free arc and short linear continuations along the true flat segment; the derivative is globally Hölder and never zero. No Hölder-speed assertion for the original exterior Cauchy parameter is needed. |
| Physical candidate | The constructed A ∘ F⁻¹ gives the actual classical Poisson equation, explicit gradient, positive Poisson-variance formula, a globally continuous zero extension and free-arc/infinity gradient limits. From Hölder spectral data and the concrete linear Hilbert equation, finite value/gradient Lᵖ bounds, actual H¹₀ membership, the full weak torsion equation and identification with the constructed Lax–Milgram solution are proved. |
| Direct boundary admission | Positive smooth interior data with continuous global zero extension and finite actual value/gradient L² norms admit explicit compact smooth approximants. This proves H¹₀ membership without a boundary trace theorem. |
| Restricted spectral form | Concrete Fourier injectivity, strict energy positivity, weighted L² form algebra, positive eigenvalue/Rayleigh quotient and distinct-eigenvalue orthogonality. Reflection, sum and scalar closure of the actual defining core/form domain, reflection of actual weak eigenfunctions, a.e. representative invariance and even/odd form and L² orthogonality. Every supplied nonzero eigenspace contains a nonzero even or odd eigenfunction. The separate compact-resolvent construction now selects the first two eigenpairs; parity of the second requires the further comparison described below. Actual compact smooth tests have finite energy and belong to the restricted form domain. |
| Fractional coercivity | Actual Schwartz Parseval is proved from mathlib inversion and Fubini with the exact source normalization. A frequency split and the defining core closure prove `∫ f² ≤ (8/π) * energy f f` for every actual restricted form member, hence `π/8 ≤ a` for every actual weak eigenpair. No compactness or eigenpair existence is inferred from this estimate alone. |
| Actual restricted spectral construction | The original core closure is identified with a closed complete Hilbert graph. Its actual value embedding is compact by Fourier-window Ascoli and uniform frequency tails. Lax–Milgram constructs the positive self-adjoint compact resolvent, and verified compact spectral theorems construct normalized first and second original weak eigenpairs, with orthogonality and both original-form min–max bounds. The first can be chosen even and nonnegative; strict Markov contraction proves its simplicity and the strict first–second gap. |
| Odd sector and strict lattice calculus | Actual Gagliardo/Fourier identities prove absolute-value and odd-fold contractions over the original form domain, plus strict gaps for sign changes. The actual least odd eigenpair has a pointwise odd zero-exterior representative nonnegative on the positive half line and strictly positive a.e. on `(0,1)`. A direct actual Fourier estimate places every even mean-zero form member above `63/20`, strictly above π. An explicit smooth-core approximation admits the zero-extended polynomial `x(1−x²)(1−x²/2)` with Rayleigh quotient below `63/20`. The resulting comparison identifies the least odd value with the actual second value and proves simplicity of the full second eigenspace. |
| Unconditional integrated-profile regularity | Every actual L² profile gives a globally one-half Hölder height with the sharp L² modulus. Actual odd weak eigenfunctions satisfy the integrated Fourier equation without any continuity assumption. Its genuine Cauchy boundary value is classically differentiable in the interval, with derivative `−aY+b`, proved by compact-test pairing and weak derivative separation. Constructed complex primitives, Schwarz reflection and an integrating-factor continuation prove a local holomorphic extension of the actual height Cauchy transform across the interval, hence interior real analyticity of the height. The actual function `−deriv (height φ)` inside the interval, zero outside, is proved a.e. equal to the original weak profile by localized integration by parts. This constructs a genuine interior analytic second eigenfunction satisfying the original weak equation, with the proved symmetry, normalization and sign. The actual Cauchy derivative equation, analytic continuation, a quadratic bound at a hypothetical zero, and a dominated double-pole limit prove strict positivity at every positive interior point by the genuine odd-kernel sign. These steps feed the subsequent actual endpoint and concavity proofs. |
| Actual semicircle barrier | The concrete zero-exterior semicircle belongs to the original closed form and satisfies `energy b ψ = ∫ ψ` for every original form test. Its genuine Cauchy transform is identified with an explicitly constructed holomorphic square-root branch by bounded holomorphic uniqueness. Small-support Fourier coercivity and actual positive-part comparison prove `|φ₂| ≤ C b`, hence actual global continuity, boundedness and square-root endpoint decay. |
| Whole-line operator and concavity | Absolute Fubini proves that the actual exterior residual is L¹. Genuine smooth interior/exterior Schwartz partitions and shrinking endpoint tests prove the whole-line weak equation, excluding endpoint distributions. Exact source Fourier pairings identify the actual `|ξ|` multiplier and its square. The resulting pointwise identity gives `φ₂″ < 0` on `(0,1)` and strict concavity on the entire closed positive half interval. No Hölder premise is used in this composition argument. |
| Complete second spectral profile | The independent square-root barrier estimate, actual concavity and interior analyticity give global `HolderWith C (1/2) secondEigenfunction`, including both endpoints and its zero extension. `exists_second_restricted_spectral_profile` collects the constructed eigenpair, normalization, symmetry, strict positivity, simplicity, analyticity, strict concavity and global Hölder regularity with no spectral hypotheses. `secondEigenfunction_linear_hilbert_equation` constructs its unique pointwise Hilbert constant. |
| Integrated spectral equation | From exactly `IsRestrictedEigenfunction a φ`, continuity and oddness: Fourier differentiation, actual height primitive commutation, finite energy of the height, and a uniquely determined constant b satisfying `energy (height φ) ψ = a * ∫ height φ * ψ - b * ∫ ψ` for every concrete compact smooth interval test. No Hilbert equation is assumed here. The absolutely convergent damped multiplier, Fubini pairing, actual Cauchy trace limit and distributional test separation now identify this Fourier distribution with the concrete continuous trace. `IsRestrictedEigenfunction.linear_hilbert_equation` proves the unique pointwise equation on the interval without assuming it. |
| Actual marked Cauchy flux | The physical formula is the actual weak torsion solution and the image is marked; comparison with its constructed smooth marked representative proves `torsionFlux (cauchyImage φ) = b/a = N/(2M)`, and its lower bound on the actual interior essential gradient norm, from the stated Hölder/sign/odd/exterior data and the explicit linear Hilbert equation. |
| Harmonic marked-kernel candidate | The concrete function `Im (cauchyInverse φ w) / mass φ` is positive and harmonic in the actual image, has the exact half-plane pullback and free-arc gradient limits. Its boundary gradient-norm product with actual physical torsion tends to `1/(2aM)`. Actual inward/outward unit normals, strict interior supports and signed normal-derivative limits are proved, including arbitrary physical interior approaches and their constant product. The physical weak Green equation and straight inward-normal source derivative now identify this function with the Green-defined marked Poisson kernel. `second_signed_poisson_stationarity` proves the canonical signed stationarity condition for that actual kernel. The localized Hadamard theorem now uses this actual Green-defined normalization. |
| Actual radial reference | Strict radial transversality gives the actual boundary argument homeomorphism from [-1,1] to [0,π]. Its inverse constructs a positive continuous actual radius, including equal positive endpoint radii. The radial domain of that profile is proved equal to the actual Cauchy image; its angular area is aN/2, squared angular L² norm is aN and actual torsion flux is b/a. No radial representation is assumed. |
| Actual normalized candidate | `IsRestrictedEigenfunction.normalized_cauchy_candidate` constructs the displayed normalized image as a genuine area-one convex domain and proves its interior essential-gradient norm is at least the spectral constant. `spectralConstant_le_cStar` proves the corresponding lower bound for the actual constructed weak Dirichlet theory without a reference certificate or universal upper bound. |
| Canonical reference assembly | `secondMoments`, `secondCauchyDomain`, `secondRadialProfile` and `secondCalibrationDensity` are actual fixed objects built from the constructed second eigenfunction. Their moment identity, Euclidean area, genuine weak torsion, exact marked flux, signed candidate stationarity, Euler identity, sharp density normalization and area-one lower bound have no spectral premises. The original final bridge is now constructed using the proved universal inequality, with no remaining field. |
| Concrete kernels | The explicit half-plane logarithmic kernel is symmetric, positive off its pole, zero on the real boundary, classically harmonic off the pole, and has the exact logarithmic singularity. The fundamental solution has outward circle flux −1 and its exact weak source identity at every pole is proved against actual compact smooth tests. The reflected Green kernel has a genuinely integrable test pairing and satisfies the exact weak equation `−ΔG = δ` against every compact smooth half-plane test. The actual Poisson density integrates to one and equals the inward source derivative. The coordinate at infinity and actual inverse map give the marked source quotient along the analytic infinity chart and conformal pullback formulas. The weak source identity now also holds on the physical image, by a smooth harmonic regular part including the pole. Compact smooth boundary data now have an actual finite-energy harmonic lift, with exact boundary values and marked action. Its weak gradient enters the proved material correction identity. |
| Radial endpoint calibration | Explicit continuous endpoint cutoffs give actual increasing lower radial domains and genuine torsion-flux convergence. Dominated convergence passes the angular integrals to the limit. Quantitative dilation sandwiches give uniform radial flux continuity; support-preserving smooth approximation extends compact smooth perturbation inequalities to continuous ones. The general radial calibration implication is proved, and the actual canonical localized derivative now discharges its shape-calculus input. |
| Domain-limit gradient bounds | Strong L² convergence passes actual interior essential-gradient bounds along increasing domains. An exact nested-domain energy identity and physical fourth-power rigidity scaling give quantitative convergence under outer dilation sandwiches. Convex metric thickening gives the needed sandwiches, without assuming monotonicity, boundary regularity or a Lipschitz trace theorem for the limiting argument. |
| Actual physical Green equation | The divided difference `dslope (cauchyInverse φ) v` is holomorphic and nowhere zero, including at the pole. Its logarithmic modulus gives a genuinely smooth harmonic regular part. `physicalGreen_weak_source` proves the physical mass-one weak Green equation, with actual compact-test pairing integrability. `physicalGreen_boundary_tendsto` proves the zero Dirichlet trace on the entire actual frontier, including the marked point. |
| Green-defined Poisson stationarity | The infinity chart preserves the imaginary axis and has positive scalar derivative. A genuine local scalar inverse gives the source derivative along the straight physical normal, not just a tangent chart curve. `physicalMarkedPoisson` is defined by that derivative and proved equal to the harmonic candidate; the actual second reference satisfies signed stationarity for it. |
| Harmonic boundary action | The actual Cauchy integral of compact boundary data, composed with the genuine inverse, gives a harmonic physical lift, correct finite-boundary values and marked inward derivative `(∫ g)/M`. Its actual value and gradient have every restricted Lᵖ bound, including L²; a continuous function on the full physical closure realizes all boundary values. This concrete action is used to evaluate the actual shape derivative. |
| Smooth convex outer construction | Normalized bump convolution uniformly smooths the actual convex Minkowski gauge. A small squared norm makes a strongly convex defining function. The constructed outer domain has strictly convex closure, a regular smooth level boundary, exact metric containments, and actual area/H¹ convergence. `G_area_bound_of_smooth_strictConvex` discharges all approximation and limiting steps and leaves only the sharp comparison on smooth competitors. |
| Actual shape transport | Every compact smooth planar vector field gives a common small parameter interval and an actual global smooth deformation diffeomorphism. Jacobian bounds prove measure domination and L² estimates. Original compact smooth approximants prove two-way `MemH10` transport. The actual weak torsion equation pulls back to the fixed domain for every original H¹₀ test. The energy operator is identified with the actual Jacobian/inverse differential formula; its first variations and the actual forcing variation are proved. Genuine bounded-continuous scalar coefficient fields prove the Jacobian, inverse Jacobian and all energy-entry derivatives in global supremum norm, on a common neighborhood identified with the actual coefficients. The actual bounded forms and their original graph integrals are now constructed. The proved Lax–Milgram base unit and differentiable inverse give the actual strong H¹ material solution derivative, identified with pullbacks of genuine deformed weak torsion. Its differentiated variational equation is proved for the original graph tests. |
| Localized Hadamard formula | Compact smooth angular perturbations are realized by actual smooth compact physical deformations, fixing neighborhoods of the marked point and both joins. Spectral analytic continuation gives actual smooth inverse/gradient extensions on the displaced free arc. Signed zero-boundary admission proves the convection/harmonic correction belongs to the original H¹₀ graph; compact-test uniqueness identifies its gradient with the actual material derivative. Fixed reflection kernels pass the strong L² gradient quotient to the actual marked flux. `torsionFlux_cauchy_boundary_hadamard` gives the oriented `q k (V·ν) ds` formula, and `cauchy_radial_torsionFlux_hasDerivAt` gives the exact angular coefficient `1/(2aM)`. `second_localized_hadamard`, `second_radial_calibration` and `second_radial_bound` have no spectral or shape premises. |
| Crude slab barrier | The actual weak torsion solution on any bounded open set inside a slab lies below its explicit one-dimensional quadratic torsion barrier. Linear distance bounds and pointwise continuous-representative corollaries require no convexity or curved-boundary trace theorem. |
| Supporting convex geometry | Actual unit support normals and nearest frontier points are constructed by separation and maximal interior balls. Orthogonal transformations preserve the original H¹₀ graph, weak PDE, area and G. Positive continuous gauge profiles give exact radial outer domains with convergent actual area. |
| Uniform marked outer comparison | Tiny flat convex outer hulls have an explicit uniform half-ball radius from a fixed inball and displacement bound. Their square-root area loss is bounded by the actual dilation factor. Caccioppoli, fixed convolution derivatives and odd reflection give uniform actual normal-quotient Taylor estimates. |
| Actual convex torsion regularity | Local Weyl representatives glue to a smooth interior representative of the original value and gradient. A genuine slab barrier and nearest supporting points prove a continuous zero extension and a finite global Lipschitz bound for every original convex domain. |
| Universal sharp gradient bound | Actual compact-test truncation energy proves a maximum principle on arbitrary bounded open sets. Weak translation comparison turns approximate sharp boundary collars into an exact Lipschitz bound. Local gradient identification then bounds the original essential supremum for every original convex competitor. |
| Unconditional final optimization | `second_universal`, `secondReferenceCertificate`, `secondSpectralBridge` and `second_exact_value` discharge the final original interfaces and prove the exact area-one supremum and attainment by the actual normalized Cauchy image, without mathematical proof parameters. |
| Normalization and stability | Exact candidate-constant algebra; actual Cauchy-image normalization invariance; Hilbert and continuous-profile quadratic deficits, including the coefficient c/4 and endpoint-inclusive rigidity. |

These are mathematical proofs over the original concrete definitions, rather
than new structures that merely restate their desired conclusions.

## Main entry points

`Torsion.torsionTheory` is an actual constructed weak Dirichlet theory.
`Torsion.ScalingLaw.proved` supplies its physical scaling law.

The unconditional final entry point is:

```lean
Torsion.second_exact_value :
  torsionTheory.cStar = ENNReal.ofReal
    (Spectral.spectralConstant Spectral.secondEigenvalue Spectral.secondEigenfunction) ∧
  ∃ D : ConvexDomain,
    D.carrier = Spectral.normalizedImage Spectral.secondEigenvalue Spectral.secondEigenfunction ∧
    D.area = 1 ∧ torsionTheory.G D = ENNReal.ofReal
      (Spectral.spectralConstant Spectral.secondEigenvalue Spectral.secondEigenfunction)
```

Additional proved entry points include:

```lean
Torsion.markedFluxExistence_proved
Torsion.torsionFlux_radial_concaveOn
Torsion.torsionFlux_tendsto_of_exhaustion
Torsion.Spectral.cauchy_injOn_upperHalfPlane
Torsion.Spectral.quadratic_identity_of_holder_boundary_equation
Torsion.Spectral.physicalCandidate_isWeakTorsion
Torsion.Spectral.physicalCandidate_eq_solutionOn
Torsion.Spectral.IsRestrictedEigenfunction.height_equation_unique
Torsion.Spectral.IsRestrictedEigenfunction.linear_hilbert_equation
Torsion.Spectral.IsRestrictedEigenfunction.cauchy_torsion_construction
Torsion.Spectral.IsRestrictedEigenfunction.cauchy_reference_geometry
Torsion.Spectral.IsRestrictedEigenfunction.normalized_cauchy_candidate
Torsion.Spectral.IsRestrictedEigenfunction.spectralConstant_le_cStar
Torsion.Spectral.MemRestrictedFormDomain.fractional_poincare
Torsion.Spectral.IsRestrictedEigenfunction.exists_even_or_odd
Torsion.Spectral.exists_first_two_restricted_eigenpairs_even_nonnegative_first
Torsion.Spectral.firstEigenvalue_lt_secondEigenvalue
Torsion.Spectral.leastOddEigenvalue_eq_secondEigenvalue
Torsion.Spectral.secondEigenvalue_le_of_isRestrictedEigenfunction_ne_first
Torsion.Spectral.secondEigenfunction_isRestrictedEigenfunction
Torsion.Spectral.secondEigenfunction_analyticOnNhd
Torsion.Spectral.secondEigenfunction_simple
Torsion.Spectral.secondEigenfunction_pos_ae
Torsion.Spectral.secondEigenfunction_pos
Torsion.Spectral.exists_second_analytic_simple_restricted_eigenfunction
Torsion.Spectral.exists_second_positive_analytic_simple_restricted_eigenfunction
Torsion.Spectral.secondEigenfunction_concaveOn
Torsion.Spectral.secondEigenfunction_strictConcaveOn
Torsion.Spectral.secondEigenfunction_holder_half
Torsion.Spectral.secondEigenfunction_linear_hilbert_equation
Torsion.Spectral.exists_second_restricted_spectral_profile
Torsion.Spectral.secondEigenfunction_sqrt_boundary_bound
Torsion.Spectral.semicircleBarrier_weak_equation
Torsion.Spectral.cauchyImage_isMarked
Torsion.Spectral.cauchyBoundaryHomeomorph
Torsion.Spectral.cauchyClosureHomeomorph
Torsion.Spectral.cauchyImage_convex
Torsion.Spectral.area_cauchyImage_eq_half_squareMass
Torsion.Spectral.cauchyJoinedBoundary_regular_frontier_charts
Torsion.Spectral.radialDomain_cauchyRadialProfile_eq
Torsion.Spectral.radialArea_cauchyRadialProfile
Torsion.Spectral.frontier_cauchyImage_freeArc_union_segment
Torsion.Spectral.cauchyAtInfinity_hasDerivAt_zero
Torsion.Spectral.cauchy_boundary_deriv_holderOn
Torsion.Spectral.torsionFlux_cauchyImage
Torsion.Spectral.secondMoments
Torsion.Spectral.secondCauchyDomain_isWeakTorsion
Torsion.Spectral.secondCauchyDomain_area
Torsion.Spectral.secondCauchyDomain_flux
Torsion.Spectral.secondCalibrationDensity_euler
Torsion.Spectral.secondCalibrationDensity_constant
Torsion.Spectral.second_spectralConstant_le_cStar
Torsion.Spectral.second_radial_bound_of_smooth_local_derivative
Torsion.RadialCalibration.calibration_of_smooth_local_derivative
Torsion.HalfPlane.integral_poisson
Torsion.HalfPlane.fundamental_circle_flux
Torsion.HalfPlane.green_weak_source
Torsion.HalfPlane.green_hasDerivAt_boundary_source
Torsion.Spectral.physicalGreen_marked_source_quotient_tendsto
Torsion.DirichletTheory.G_area_bound_of_exhaustion
Torsion.DirichletTheory.G_area_bound_of_outer_approximation
Torsion.secondSpectralBridge_of_universal
Torsion.Spectral.physicalGreen_weak_source
Torsion.Spectral.physicalGreen_marked_normal_source_hasDerivWithinAt
Torsion.Spectral.physicalMarkedPoisson_eq_kernel
Torsion.Spectral.second_signed_poisson_stationarity
Torsion.Spectral.physicalHarmonicLift_marked_normal_tendsto
Torsion.ConvexDomain.exists_smooth_strictConvex_outer_sequence
Torsion.DirichletTheory.G_area_bound_of_smooth_strictConvex
Torsion.secondSpectralBridge_of_smooth_comparison
Torsion.Shape.exists_MemH10_transport_deformation
Torsion.Shape.exists_weakTorsion_pullback_deformation
Torsion.Shape.uniformEnergyCoefficient_hasDerivAt_zero
Torsion.IsWeakTorsion.le_slab_barrier
Torsion.DirichletTheory.G_le_second_spectral_bound
Torsion.second_universal
Torsion.secondReferenceCertificate
Torsion.secondSpectralBridge
Torsion.second_exact_value
```

The older analytic entry points still expose their reusable linear Hilbert
input. It is now derived by `IsRestrictedEigenfunction.linear_hilbert_equation`
from the original weak spectral equation, oddness and Hölder regularity.
The newer `IsRestrictedEigenfunction.*` construction entry points do not
assume the Hilbert equation, convexity, geometric area, weak torsion or marked
flux. Their concavity and global Hölder inputs are now proved for the constructed
`secondEigenfunction`. These general interfaces retain their parameters for
reuse with other profiles; they are no longer missing spectral inputs for
the canonical second profile.

`Torsion.exact_value_of_spectralBridge` and `Torsion.exact_value_of_reference`
remain reusable general theorems. Their bridge and certificate parameters are
inhabited by the actual canonical objects above. Earlier source comments
record the conditional status at the time those modules were introduced;
`CanonicalOptimization` is the final unconditional assembly.

## Scope of completion

The main exact spectral optimization theorem is unconditional. No field of
its original `ReferenceCertificate` or `SpectralBridge` remains open. The
universal inequality bounds the actual interior essential gradient norm of
all original convex competitors; it does not infer an upper bound on G from
the previously proved inequality Q ≤ G.

The exact localized boundary formula is proved on the spectral Cauchy
references, including the unconditional canonical second reference. The
broader non-spectral version of manuscript Lemma 4.1 for arbitrary smooth
radial reference arcs is not asserted here. Actual localized radial flux
differentiability itself is proved for every positive continuous reference
profile. No competitor class or optimization constant was changed.


Appendix A's benchmarks/minimization and Appendix B's numerical illustration
are not complete formal theorems here. Radial rigidity does not classify all
convex maximizers, in line with Remark 8.2.

## Reuse of existing formalizations

This development uses the pinned mathlib throughout. The latest progress
reuses its Schwartz Fourier inversion and bilinear Fubini theorem, complex
exponential half-line integrals, dominated/parameter-integral continuity,
distributional compact-test separation, finite-dimensional Jacobian change of
variables, rectangular Green identity, compact parameter spaces, closed embeddings
and convex topology. The dependency pins remain unchanged; the reusable
external spectral and complex-analysis proofs are backported as described below.

The spectral construction includes a selective Apache-2.0 backport from
[compact-spectral](https://github.com/abenenson/compact-spectral/tree/72cd62dbdd4c397d26fc0c5777d60fea2211e938),
with attribution and its license in `Torsion/CompactSpectral`. Its weak Hilbert
compactness and Rayleigh arguments are compiled and audited in the pinned Lean
4.19 environment. The actual restricted compact embedding and the connection
of these abstract results to the original weak Fourier problem are proved
here. The external repository is not an unverified dependency or an axiom.
The [rellich-kondrachov](https://github.com/abenenson/rellich-kondrachov/tree/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23)
source was inspected but is not needed: the actual compact embedding uses
mathlib Ascoli on Fourier windows and the proved original-energy tail bound.

Interior spectral regularity also uses verified selective Apache-2.0 backports
of [mathlib's complex primitive construction](https://github.com/leanprover-community/mathlib4/blob/8fe7ce475b056f0b266d7107893f2c4d772c712f/Mathlib/Analysis/Complex/HasPrimitives.lean)
and [TauCeti's Schwarz reflection proofs](https://github.com/TauCetiProject/TauCeti/tree/e6b5f42c62ab0484faf5c0e66079de65bcc138a2/TauCeti/Analysis/Complex/Conformal/Reflection).
Their attribution is retained in the source files, with the license in
`Torsion/ComplexAnalysis/LICENSE`. These proofs are adapted, compiled and
included in the project-wide axiom audit under the unchanged Lean/mathlib
4.19 pins. The actual weak spectral-to-analytic continuation argument and
the canonical representative identification are proved here.

## File organization

- `Definitions`, `Sobolev*`, `WeakGradient`, `Poincare`, `BoundedDomains`,
  `HilbertDirichlet`, `Dirichlet*`, `TorsionPositivity`: the concrete weak PDE.
- `Dilation*`: physical geometric and PDE scaling.
- `WeakReflection*`, `WeakHarmonicWeyl*`, `MarkedBoundaryRegularity`,
  `MarkedFlux*`: actual local regularity, marked flux and its comparison laws.
- `RadialConcavity*`, `RadialGeometry`, `RadialFluxConcavity*`: radial domains
  and concavity, including the actual constructed-flux theorem in `MarkedFlux`.
- `CauchyTransform*`, `CauchyConformalGeometry*`, `CauchySpectralIdentity`,
  `Spectral*`, `RestrictedSpectral*`, `Curvature*`: actual boundary analysis,
  conformal geometry and spectral-form foundations.
- `PhysicalCauchy*`, `PhysicalTorsionCalculus`, `SobolevBoundaryAdmission`:
  the constructed physical candidate and direct boundary admission.
- `ContinuousProfiles`, `Calibration`, `RadialCalibrationCutoff`,
  `RadialCalibrationSmooth`, `SmoothCompactApproximation`, `Stability`,
  `RadialStability`: concrete endpoint passage, smooth compact approximation,
  calibration implications and stability.
- `HalfPlaneGreen`, `HalfPlanePoisson`, `HalfPlaneGreenInfinity`,
  `HalfPlaneGreenSource`, `HalfPlaneGreenSourceTranslation`, `PhysicalCauchyGreen`: explicit logarithmic and Poisson kernel analysis.
- `GradientBoundExhaustion`, `OuterDomainConvergence`, `OuterGradientBounds`,
  `ConvexOuterDilation`, `TorsionTranslation`, `ConvexOuterApproximation`:
  actual weak PDE convergence, physical translation covariance and passage
  of bounds for every original convex domain.
- `CanonicalSpectralCandidate`, `CanonicalRadialCalibration`,
  `CanonicalSmoothReduction`: constructed canonical reference objects and
  preserved general conditional reductions.
- `ConformalGreenRegularPart`, `ClassicalWeakLaplacian`, `GreenRegularPart`,
  `PhysicalCauchyGreenWeak`, `PhysicalCauchyGreenBoundary`, `PositiveLocalInverse`, `PhysicalCauchyGreenNormal`,
  `PhysicalCauchyPoisson`, `PhysicalCauchyHarmonic*`: actual physical weak kernels,
  normal source, stationarity and harmonic boundary action.
- `ConvexMollification`, `SmoothConvexLevelSets`, `SmoothConvexOuterApproximation`,
  `SmoothConvexReduction`: actual smooth strictly convex approximations.
- `Shape*`: actual smooth deformations, Jacobian control, L² and Sobolev
  transport, forcing and fixed-domain energy calculations.
- `SlabTorsionBarrier`: actual quadratic slab comparison and local pointwise bounds.
- `ConvexGaugeRadial`, `ConvexSupportingRadial`, `CanonicalSupportingFlux`:
  actual radial enlargements and sharp supporting-boundary comparison.
- `ConvexSupportingPoint`, `NormalFrame*`, `SobolevIsometry`, `TorsionIsometry`,
  `SupportedConvexFlatHull*`, `FlatOuterHullArea`: uniform supporting geometry.
- `ConvolutionDerivativeBounds`, `LocalHarmonicBound`, `HarmonicNormalTaylor`,
  `MarkedTorsionTaylor`, `MarkedHullCollarComparison`: genuine uniform Taylor bounds.
- `WeakTorsionInterior`, `WeakTorsionRepresentative`, `ConvexTorsionContinuity`,
  `WeakTranslationLipschitz`, `BoundaryCollarGradient`, `UniformSupportedCollar`:
  actual regularity, weak maximum principle and sharp boundary collars.
- `CanonicalUniversal`, `CanonicalOptimization`: unconditional universal bound,
  original final certificates, exact optimum and attainment.
- `Main`, `SpectralMain`, `ProvedMain`: preserved reusable theorem assembly.

Only source, configuration, documentation and validation output are packaged;
no toolchain binaries, local dependency symlinks or build cache are included.

## Localized shape-calculus entry points

- `ShapeMaterialSolution`, `ShapeMaterialIdentification`, `ShapeMaterialEulerian`:
  actual strong material differentiation and original weak-PDE identification.
- `RadialDeformation`, `ShapeMarkedFluxDerivative`: concrete angular
  deformations and genuine fixed-patch marked-flux differentiation.
- `CauchyShapeCorrection`, `CauchyShapeHadamard`,
  `CauchyHadamardBoundaryIntegral`: actual H¹₀ correction, material-gradient
  identification and the physical oriented Hadamard integral.
- `CauchyRadialHadamard`, `CanonicalHadamard`: exact angular formula and the
  unconditional canonical radial supporting inequality and sharp bound.

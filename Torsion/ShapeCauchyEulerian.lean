module

public import Torsion.ShapeEulerianCommutator
public import Torsion.CanonicalSpectralCandidate
public import Torsion.CauchyBoundaryStationarity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Eulerian commutator and boundary lift data of the actual spectral torsion

The interior commutator is specialized to the constructed canonical second
domain, without a spectral or PDE premise. The negative convection has the
actual physical boundary trace `q V·ν` along arbitrary interior approaches.
This identifies the prospective Eulerian Dirichlet data; it does not assert
that the actual material derivative has a pointwise zero boundary trace.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion.Spectral

/-- The proved commutator on the actual canonical second spectral domain,
using its actual smooth torsion function and actual classical Poisson PDE. -/
theorem second_eulerian_commutator {V : Plane → Plane} {ψ : Plane → ℝ}
    (hV : ContDiff ℝ ∞ V) (hψ : IsTest secondCauchyDomain.carrier ψ) :
    (∫ x, inner (𝕜 := ℝ)
      (gradient (fun y => inner (𝕜 := ℝ) (V y) (gradient (physicalCandidate secondEigenfunction) y)) x)
      (gradient ψ x)) =
      (∫ x, Shape.divergence V x * ψ x) -
        ∫ x, inner (𝕜 := ℝ)
          (Shape.energyVariationOperator V x (gradient (physicalCandidate secondEigenfunction) x))
          (gradient ψ x) := by
  apply Shape.eulerian_commutator_local_smooth_test secondCauchyDomain.isOpen hV
    (physicalCandidate_contDiffOn secondEigenfunction_continuous secondEigenfunction_odd
      secondEigenfunction_zero_exterior secondEigenfunction_pos) _ hψ
  intro x hx
  exact physicalCandidate_laplacian_eq_neg_one secondEigenfunction_continuous
    secondEigenfunction_odd secondEigenfunction_zero_exterior secondEigenfunction_pos hx

/-- The negative convective term has exactly the Eulerian boundary lift
`q (V·ν)` with the genuine outward physical normal and actual torsion flux
trace. The limit is along arbitrary physical interior approaches, and also
holds at the two joins (where a localized perturbation will vanish). -/
theorem second_negative_convection_boundary_tendsto {V : Plane → Plane}
    (hV : Continuous V) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun w => -inner (𝕜 := ℝ) (V w) (gradient (physicalCandidate secondEigenfunction) w))
      (𝓝[secondCauchyDomain.carrier] (cauchyExtension secondEigenfunction (t : ℂ)))
      (𝓝 ((‖cauchyDerivativeExtension secondEigenfunction (t : Plane)‖ / (2 * secondEigenvalue)) *
        inner (𝕜 := ℝ) (V (cauchyExtension secondEigenfunction (t : ℂ)))
          (cauchyOutwardNormal secondEigenfunction t))) := by
  have hg := gradient_physicalCandidate_tendsto_at_freeArc
    secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos secondHolderConstant_spec
    (by norm_num) (by norm_num) secondEigenfunction_odd secondEigenfunction_zero_exterior
    secondEigenfunction_pos secondBoundaryConstant_equation ht
  have hv : Tendsto V (𝓝[cauchyImage secondEigenfunction] (cauchyExtension secondEigenfunction (t : ℂ)))
      (𝓝 (V (cauchyExtension secondEigenfunction (t : ℂ)))) :=
    (hV.tendsto (cauchyExtension secondEigenfunction (t : ℂ))).mono_left nhdsWithin_le_nhds
  have h := (hv.inner hg (𝕜 := ℝ)).neg
  simpa only [secondCauchyDomain_carrier, real_inner_smul_right,
    cauchyOutwardNormal, inner_neg_right, mul_neg] using h

end Torsion.Spectral

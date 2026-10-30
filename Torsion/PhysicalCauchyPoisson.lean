import Torsion.PhysicalCauchyGreenWeak
import Torsion.PhysicalCauchyGreenNormal
import Torsion.CauchyBoundaryStationarity
import Torsion.CanonicalSpectralCandidate

/-!
# The marked Poisson kernel defined by the actual Green source derivative

The Green kernel satisfies the proved weak mass-one equation. Its physical
inward source derivative now identifies the earlier harmonic candidate with
the actual marked Poisson kernel. Signed free-boundary stationarity therefore
holds for this Green-defined kernel, including for the canonical second
spectral reference. A Hadamard shape derivative is a separate theorem.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The marked Poisson kernel defined by the physical unit inward-normal
source derivative of the actual Green function at the flat marked point. -/
def physicalMarkedPoisson (φ : ℝ → ℝ) (w : Plane) : ℝ :=
  derivWithin
    (fun t : ℝ => if t = 0 then 0 else physicalGreen φ w ((t : Plane) * Complex.I))
    (Ici 0) 0

/-- The actual source derivative equals the previously constructed harmonic
function, with its normalization fixed by the weak Green equation. -/
theorem physicalMarkedPoisson_eq_kernel {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ cauchyImage φ) :
    physicalMarkedPoisson φ w = physicalMarkedKernel φ w :=
  (physicalGreen_marked_normal_source_hasDerivWithinAt hφ hodd hzero hpos hw).derivWithin
    (uniqueDiffOn_Ici 0 0 left_mem_Ici)

theorem gradient_physicalMarkedPoisson_eq_kernel {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ cauchyImage φ) :
    gradient (physicalMarkedPoisson φ) w = gradient (physicalMarkedKernel φ) w := by
  apply Filter.EventuallyEq.gradient_eq
  filter_upwards [(cauchyImage_isOpen hφ hodd hzero hpos).mem_nhds hw] with z hz
  exact physicalMarkedPoisson_eq_kernel hφ hodd hzero hpos hz

theorem physicalMarkedPoisson_pos {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ cauchyImage φ) : 0 < physicalMarkedPoisson φ w := by
  rw [physicalMarkedPoisson_eq_kernel hφ hodd hzero hpos hw]
  exact physicalMarkedKernel_pos hφ.continuousOn hpos hw

/-- The constant signed stationarity condition now uses the Poisson kernel
defined from the physical normal-source derivative of the actual Green
function, along arbitrary physical interior approaches to the free arc. -/
theorem signed_stationarity_physicalCandidate_poisson_tendsto_at_freeArc
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun w =>
      (-inner (𝕜 := ℝ) (gradient (physicalCandidate φ) w) (cauchyOutwardNormal φ t)) *
      (-inner (𝕜 := ℝ) (gradient (physicalMarkedPoisson φ) w) (cauchyOutwardNormal φ t)))
      (𝓝[cauchyImage φ] (cauchyExtension φ (t : Plane)))
      (𝓝 (1 / (2 * a * mass φ))) := by
  apply (signed_stationarity_physicalCandidate_kernel_tendsto_at_freeArc
    ha hφ hα0 hα1 hodd hzero hpos hlinear ht).congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [gradient_physicalMarkedPoisson_eq_kernel (hφ.continuous hα0) hodd hzero hpos hw]

/-- The canonical actual second spectral domain satisfies signed stationarity
for the actual Green-defined marked Poisson kernel, with no spectral or
kernel-identification assumptions. -/
theorem second_signed_poisson_stationarity {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun w =>
      (-inner (𝕜 := ℝ) (gradient (physicalCandidate secondEigenfunction) w)
        (cauchyOutwardNormal secondEigenfunction t)) *
      (-inner (𝕜 := ℝ) (gradient (physicalMarkedPoisson secondEigenfunction) w)
        (cauchyOutwardNormal secondEigenfunction t)))
      (𝓝[secondCauchyDomain.carrier] (cauchyExtension secondEigenfunction (t : Plane)))
      (𝓝 secondMoments.stationarity) :=
  signed_stationarity_physicalCandidate_poisson_tendsto_at_freeArc
    secondEigenfunction_isRestrictedEigenfunction.eigenvalue_pos
    secondHolderConstant_spec (by norm_num) (by norm_num) secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos secondBoundaryConstant_equation ht

end Torsion.Spectral

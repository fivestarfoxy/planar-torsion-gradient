module

public import Torsion.PhysicalCauchySobolev
public import Torsion.ClassicalWeakTorsion
public import Torsion.SobolevUniqueness

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Identification of the physical Cauchy formula as actual weak torsion

Actual H¹₀ density and the calculated classical Poisson equation now imply
the original full weak equation. Uniqueness identifies this constructed
formula with every weak solution on the actual Cauchy image.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace Torsion

/-- Global value uniqueness needs boundedness and measurability, not
convexity or boundary regularity. -/
theorem IsWeakTorsion.value_global_ae_eq_of_bounded {D : Set Plane}
    (hD : MeasurableSet D) (hb : Bornology.IsBounded D)
    {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hv : IsWeakTorsion D v h) : u =ᵐ[volume] v := by
  have hgrad := hu.gradient_global_ae_eq hD hv
  have htest := hu.1.sub hv.1
  have hdiffgrad : (fun x => g x - h x) =ᵐ[volume] 0 := by
    filter_upwards [hgrad] with x hx
    simp only [hx, sub_self, Pi.zero_apply]
  have hgradnorm : eLpNorm (fun x => g x - h x) 2 volume = 0 :=
    (eLpNorm_eq_zero_iff (by norm_num)).mpr hdiffgrad
  obtain ⟨K, _, hP⟩ := exists_poincare_constant_of_bounded hb
  have hvaluenorm : eLpNorm (fun x => u x - v x) 2 volume = 0 := by
    apply le_antisymm
    · simpa only [hgradnorm, mul_zero] using hP _ _ htest
    · exact zero_le
  have hdiffvalue := (eLpNorm_eq_zero_iff (by norm_num)).mp hvaluenorm
  filter_upwards [hdiffvalue] with x hx
  exact sub_eq_zero.mp hx

namespace Spectral

/-- The actual Cauchy candidate satisfies the full weak torsion equation,
with no boundary-admissibility or weak-equation hypothesis. -/
theorem physicalCandidate_isWeakTorsion {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    IsWeakTorsion (cauchyImage φ) (physicalZeroExtension φ) (physicalZeroGradient φ) := by
  have hcont := hφ.continuous hα0
  have hD := cauchyImage_isOpen hcont hodd hzero hpos
  apply isWeakTorsion_of_classical_poisson hD (cauchy_image_isBounded hcont hodd hzero)
    (physicalCandidate_memH10 ha hφ hα0 hα1 hodd hzero hpos hlinear)
    (physicalZeroExtension_contDiffOn hcont hodd hzero hpos)
  · filter_upwards [ae_restrict_mem hD.measurableSet] with w hw
    exact physicalZeroGradient_eq_gradient_on_image hcont hodd hzero hpos hw
  · intro w hw
    exact physicalZeroExtension_laplacian_eq_neg_one hcont hodd hzero hpos hw

/-- A constructed solution record on the actual open image. Convexity is
not needed for existence or identification of its weak torsion function. -/
def physicalDirichletSolution {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) : DirichletSolution (cauchyImage φ) where
  value := physicalZeroExtension φ
  weakGradient := physicalZeroGradient φ
  weakEquation := physicalCandidate_isWeakTorsion ha hφ hα0 hα1 hodd hzero hpos hlinear

/-- Every actual weak torsion pair on the Cauchy image agrees globally
almost everywhere with the exact physical formula and its supplied gradient. -/
theorem physicalCandidate_unique {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion (cauchyImage φ) u g) :
    u =ᵐ[volume] physicalZeroExtension φ ∧ g =ᵐ[volume] physicalZeroGradient φ := by
  have hcont := hφ.continuous hα0
  have hc := physicalCandidate_isWeakTorsion ha hφ hα0 hα1 hodd hzero hpos hlinear
  exact ⟨hu.value_global_ae_eq_of_bounded
    (cauchyImage_isOpen hcont hodd hzero hpos).measurableSet
    (cauchy_image_isBounded hcont hodd hzero) hc,
    hu.gradient_global_ae_eq (cauchyImage_isOpen hcont hodd hzero hpos).measurableSet hc⟩

/-- In particular the previously constructed Lax–Milgram solution is the
physical formula, in both value and weak gradient, on this actual image. -/
theorem physicalCandidate_eq_solutionOn {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : a ≠ 0) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    let S := HilbertDirichlet.solutionOn (cauchyImage φ)
      (cauchyImage_isOpen (hφ.continuous hα0) hodd hzero hpos).measurableSet
      (cauchy_image_isBounded (hφ.continuous hα0) hodd hzero)
    S.value =ᵐ[volume] physicalZeroExtension φ ∧
      S.weakGradient =ᵐ[volume] physicalZeroGradient φ := by
  exact physicalCandidate_unique ha hφ hα0 hα1 hodd hzero hpos hlinear
    (HilbertDirichlet.solutionOn (cauchyImage φ)
      (cauchyImage_isOpen (hφ.continuous hα0) hodd hzero hpos).measurableSet
      (cauchy_image_isBounded (hφ.continuous hα0) hodd hzero)).weakEquation

end Spectral
end Torsion

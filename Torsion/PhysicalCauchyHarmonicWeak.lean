import Torsion.PhysicalCauchyHarmonicClosure
import Torsion.ClassicalWeakLaplacian

/-! # Actual weak harmonicity of the compact-data physical boundary lift -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral

theorem physicalHarmonicLift_contDiffOn {φ g : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) (hg : Continuous g) :
    ContDiffOn ℝ ∞ (physicalHarmonicLift φ g) (cauchyImage φ) := by
  intro w hw
  have hB : ContDiffAt ℝ ∞ (realCauchy g ∘ cauchyInverse φ) w :=
    ((physicalHarmonicLift_analyticOnNhd hφ hodd hzero hpos hg) w hw).contDiffAt.restrict_scalars ℝ
  exact (Complex.imCLM.contDiff.contDiffAt.comp w hB).contDiffWithinAt

/-- The actual lift annihilates every original compact smooth test under
the actual classical-gradient pairing, globally and on the physical image. -/
theorem physicalHarmonicLift_weak_equation {φ g : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) (hg : Continuous g)
    {η : Plane → ℝ} (hη : IsTest (cauchyImage φ) η) :
    Integrable (fun w => inner (𝕜 := ℝ) (gradient (physicalHarmonicLift φ g) w) (gradient η w)) ∧
      (∫ w, inner (𝕜 := ℝ) (gradient (physicalHarmonicLift φ g) w) (gradient η w)) = 0 ∧
      (∫ w in cauchyImage φ,
        inner (𝕜 := ℝ) (gradient (physicalHarmonicLift φ g) w) (gradient η w)) = 0 := by
  have hU := cauchyImage_isOpen hφ hodd hzero hpos
  have hs := physicalHarmonicLift_contDiffOn hφ hodd hzero hpos hg
  have hl : ∀ w ∈ cauchyImage φ, WeakHarmonicRegularity.planarLaplacian
      (physicalHarmonicLift φ g) w = 0 :=
    fun w hw => physicalHarmonicLift_laplacian_eq_zero hφ hodd hzero hpos hg hw
  exact ⟨classical_smooth_test_pairing_integrable hU hs hη,
    classical_harmonic_smooth_test_equation hU hs hl hη,
    classical_harmonic_set_smooth_test_equation hU hs hl hη⟩

end Torsion.Spectral

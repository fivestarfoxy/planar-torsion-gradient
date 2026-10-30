import Torsion.RestrictedSpectralConcavitySign
import Torsion.RestrictedSpectralGlobalEquation

/-!
# Concavity of genuine odd restricted eigenfunctions

The original weak equation, the proved endpoint reconstruction, and the
actual exterior residual yield the classical second-order identity and
strict concavity. No global Hölder estimate or pointwise operator formula
is among the hypotheses.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- The actual restricted spectral equation composes to the ordinary
second-order identity, including its genuine exterior forcing. -/
theorem IsRestrictedEigenfunction.second_deriv_eq_exterior_residual
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hreg : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hr : Integrable (exteriorResidualZero f))
    (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    deriv (deriv f) x = -a ^ 2 * f x - (1 / Real.pi) *
      ∫ y : ℝ, exteriorResidualZero f y / (x - y) ^ 2 :=
  hf.second_deriv_eq_of_global_schwartz_equation hreg hr
    (hf.global_schwartz_equation hr) x hx

/-- Every positive-half point of a genuine odd nonnegative spectral
eigenfunction has strictly negative ordinary second derivative. -/
theorem IsRestrictedEigenfunction.second_deriv_neg
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hreg : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hr : Integrable (exteriorResidualZero f))
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : deriv (deriv f) x < 0 :=
  hf.second_deriv_neg_of_global_schwartz_equation hodd hnonneg hreg hr
    (hf.global_schwartz_equation hr) x hx

theorem IsRestrictedEigenfunction.strictConcaveOn_Ioo
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hreg : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hr : Integrable (exteriorResidualZero f)) :
    StrictConcaveOn ℝ (Ioo (0 : ℝ) 1) f :=
  hf.strictConcaveOn_Ioo_of_global_schwartz_equation hodd hnonneg hreg hr
    (hf.global_schwartz_equation hr)

theorem IsRestrictedEigenfunction.strictConcaveOn_Icc
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hreg : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hr : Integrable (exteriorResidualZero f)) :
    StrictConcaveOn ℝ (Icc (0 : ℝ) 1) f :=
  hf.strictConcaveOn_Icc_of_global_schwartz_equation hodd hnonneg hreg hc hr
    (hf.global_schwartz_equation hr)

theorem IsRestrictedEigenfunction.concaveOn_Ioo
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hreg : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hr : Integrable (exteriorResidualZero f)) :
    ConcaveOn ℝ (Ioo (0 : ℝ) 1) f :=
  (hf.strictConcaveOn_Ioo hodd hnonneg hreg hr).concaveOn

theorem IsRestrictedEigenfunction.concaveOn_Icc
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hreg : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hr : Integrable (exteriorResidualZero f)) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) f :=
  (hf.strictConcaveOn_Icc hodd hnonneg hreg hc hr).concaveOn

end Torsion.Spectral

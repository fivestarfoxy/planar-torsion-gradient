import Torsion.RestrictedSpectralConcavityComposition
import Mathlib.Analysis.Convex.Deriv

/-!
# Strict concavity from the actual exterior residual

The positive odd paired kernel makes the exterior forcing strictly
positive. The actual composition identity therefore makes the classical
second derivative strictly negative at every positive interior point.
Ordinary one-dimensional calculus then gives strict concavity, including
the endpoints whenever the actual function is continuous there.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- The actual exterior forcing is strictly positive throughout the
positive interval. L¹ of the residual supplies all required interior
quotient integrability through the genuine support gap. -/
theorem IsRestrictedEigenfunction.exterior_potential_pos
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hr : Integrable (exteriorResidualZero f))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < ∫ y : ℝ, exteriorResidualZero f y / (x - y) ^ 2 := by
  have hrzero : ∀ᵐ y : ℝ, y ∈ Ioo (-1 : ℝ) 1 → exteriorResidualZero f y = 0 :=
    ae_of_all _ fun y hy => by
      simp only [exteriorResidualZero, if_neg (not_lt.2 (abs_lt.2 hy).le)]
  have hxfull : |x| < 1 := abs_lt.2 ⟨by linarith [hx.1], hx.2⟩
  exact hf.1.integral_exteriorResidualZero_div_sq_pos hodd hf.2.1 hnonneg hx.1
    (integrable_exterior_div_pow hr hrzero hxfull 2)

/-- The genuine composition formula and the strictly positive actual
exterior forcing imply a strictly negative ordinary second derivative.
Only a.e. half-line nonnegativity is required; interior continuity
supplies its pointwise version. -/
theorem IsRestrictedEigenfunction.second_deriv_neg_of_global_schwartz_equation
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hreg : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hr : Integrable (exteriorResidualZero f))
    (hglobal : ∀ S : 𝓢(ℝ, ℝ), energy f S =
      ∫ x : ℝ, (a * f x - exteriorResidualZero f x) * S x)
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv f) x < 0 := by
  have hpoint : 0 ≤ f x := by
    apply nonneg_on_Ioo_of_continuousOn_ae_nonneg
      (hreg.continuousOn.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩))
      (ae_restrict_of_ae_restrict_of_subset (fun t ht => ht.1) hnonneg) x hx
  have hpotential := hf.exterior_potential_pos hodd hnonneg hr hx
  have hforcing : 0 < (1 / Real.pi) *
      ∫ y : ℝ, exteriorResidualZero f y / (x - y) ^ 2 :=
    mul_pos (one_div_pos.2 Real.pi_pos) hpotential
  have hmass : 0 ≤ a ^ 2 * f x := mul_nonneg (sq_nonneg a) hpoint
  rw [hf.second_deriv_eq_of_global_schwartz_equation hreg hr hglobal x
    ⟨by linarith [hx.1], hx.2⟩]
  linarith

/-- Strict concavity on the positive open interval, derived from the
actual weak Fourier equation and actual exterior residual. -/
theorem IsRestrictedEigenfunction.strictConcaveOn_Ioo_of_global_schwartz_equation
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hreg : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hr : Integrable (exteriorResidualZero f))
    (hglobal : ∀ S : 𝓢(ℝ, ℝ), energy f S =
      ∫ x : ℝ, (a * f x - exteriorResidualZero f x) * S x) :
    StrictConcaveOn ℝ (Ioo (0 : ℝ) 1) f := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioo 0 1)
    (hreg.continuousOn.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩))
  intro x hx
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
    hf.second_deriv_neg_of_global_schwartz_equation hodd hnonneg hreg hr hglobal x hx

/-- Actual continuous endpoint values extend the strict concavity all
the way to the closed positive interval. -/
theorem IsRestrictedEigenfunction.strictConcaveOn_Icc_of_global_schwartz_equation
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hreg : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hr : Integrable (exteriorResidualZero f))
    (hglobal : ∀ S : 𝓢(ℝ, ℝ), energy f S =
      ∫ x : ℝ, (a * f x - exteriorResidualZero f x) * S x) :
    StrictConcaveOn ℝ (Icc (0 : ℝ) 1) f := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) hc
  intro x hx
  rw [interior_Icc] at hx
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
    hf.second_deriv_neg_of_global_schwartz_equation hodd hnonneg hreg hr hglobal x hx

theorem IsRestrictedEigenfunction.concaveOn_Ioo_of_global_schwartz_equation
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hreg : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hr : Integrable (exteriorResidualZero f))
    (hglobal : ∀ S : 𝓢(ℝ, ℝ), energy f S =
      ∫ x : ℝ, (a * f x - exteriorResidualZero f x) * S x) :
    ConcaveOn ℝ (Ioo (0 : ℝ) 1) f :=
  (hf.strictConcaveOn_Ioo_of_global_schwartz_equation hodd hnonneg hreg hr hglobal).concaveOn

theorem IsRestrictedEigenfunction.concaveOn_Icc_of_global_schwartz_equation
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hreg : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hr : Integrable (exteriorResidualZero f))
    (hglobal : ∀ S : 𝓢(ℝ, ℝ), energy f S =
      ∫ x : ℝ, (a * f x - exteriorResidualZero f x) * S x) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) f :=
  (hf.strictConcaveOn_Icc_of_global_schwartz_equation hodd hnonneg hreg hc hr hglobal).concaveOn

end Torsion.Spectral

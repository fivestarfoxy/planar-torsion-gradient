import Torsion.CauchyConformalGeometry.ConvexitySupport
import Torsion.CauchyConformalGeometry.ConvexityCriterion

/-!
# Convexity of the actual Cauchy image

The proved actual tangent inequalities supply a nonzero supporting
functional at every point of the actual frontier. The open bounded image
is therefore convex. This is a proof over the concrete image, not a
convex-domain certificate assumed as an additional input.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The image has a nonzero lower supporting functional at every actual
frontier point, with the free-arc normals constructed from its tangent. -/
theorem cauchyImage_frontier_support {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x) :
    ∀ p ∈ frontier (cauchyImage φ), ∃ ℓ : ℂ →L[ℝ] ℝ,
      ℓ ≠ 0 ∧ ∀ q ∈ frontier (cauchyImage φ), ℓ p ≤ ℓ q := by
  intro p hp
  rw [frontier_cauchyImage_freeArc_union_segment hφ hα0 hα1 hodd hzero hpos] at hp
  rcases hp with ⟨t, ht, rfl⟩ | ⟨r, hr, rfl⟩
  · refine ⟨cauchySupportFunctional a b φ t,
      cauchySupportFunctional_ne_zero ha hφ hα0 hα1 hodd hzero hpos hlinear ht, ?_⟩
    intro q hq
    exact sub_nonneg.1 (cauchySupport_nonneg_frontier
      ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd ht hq)
  · refine ⟨Complex.imCLM, ?_, ?_⟩
    · intro hzero
      have h := congrArg (fun ℓ : ℂ →L[ℝ] ℝ => ℓ Complex.I) hzero
      norm_num at h
    · intro q hq
      simpa only [Complex.imCLM_apply, Complex.ofReal_im] using
        cauchy_frontier_im_nonneg (hφ.continuous hα0).continuousOn hpos hq

/-- The actual Cauchy image is convex, derived from the original profile
concavity and the explicit linear Hilbert equation. -/
theorem cauchyImage_convex {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x) :
    Convex ℝ (cauchyImage φ) :=
  convex_of_frontier_support_ge
    (cauchyImage_isOpen (hφ.continuous hα0) hodd hzero hpos)
    (cauchy_image_isBounded (hφ.continuous hα0) hodd hzero)
    (cauchyImage_frontier_support ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd)

/-- The concrete Cauchy image, now equipped with its proved open, bounded,
convex and nonempty properties. -/
def cauchyConvexDomain {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x) : ConvexDomain where
  carrier := cauchyImage φ
  isOpen := cauchyImage_isOpen (hφ.continuous hα0) hodd hzero hpos
  bounded := cauchy_image_isBounded (hφ.continuous hα0) hodd hzero
  convex := cauchyImage_convex ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd
  nonempty := ⟨cauchy φ Complex.I, Complex.I, by simp [upperHalfPlane], rfl⟩

@[simp] theorem cauchyConvexDomain_carrier {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x) :
    (cauchyConvexDomain ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd).carrier = cauchyImage φ := rfl

end Torsion.Spectral

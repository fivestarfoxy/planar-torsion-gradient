module

public import Torsion.CauchyConformalGeometry.ExteriorBoundary
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual compactified boundary homeomorphism

Adjoining the single point at infinity to the real parameter line gives the
complete Cauchy boundary parametrization. The actual integral decay proves
continuity at infinity; the finite boundary injectivity and nonvanishing
already proved show that this is a homeomorphism onto the actual frontier.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal OnePoint

namespace Torsion.Spectral

/-- The actual real boundary curve, with its proved value zero at infinity. -/
def cauchyCompactifiedBoundary (φ : ℝ → ℝ) (x : OnePoint ℝ) : ℂ :=
  x.elim 0 (fun t : ℝ => cauchyExtension φ (t : ℂ))

@[simp] theorem cauchyCompactifiedBoundary_infty (φ : ℝ → ℝ) :
    cauchyCompactifiedBoundary φ ∞ = 0 := rfl

@[simp] theorem cauchyCompactifiedBoundary_coe (φ : ℝ → ℝ) (x : ℝ) :
    cauchyCompactifiedBoundary φ (x : OnePoint ℝ) = cauchyExtension φ (x : ℂ) := rfl

/-- The genuine boundary curve tends to zero along both exterior rays. -/
theorem cauchy_boundary_tendsto_zero {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) :
    Tendsto (fun x : ℝ => cauchyExtension φ (x : ℂ)) (coclosedCompact ℝ) (𝓝 0) := by
  have hn : Tendsto (fun x : ℝ => ‖(x : ℂ)‖) (coclosedCompact ℝ) atTop := by
    rw [coclosedCompact_eq_cocompact]
    apply (tendsto_norm_cocompact_atTop : Tendsto (norm : ℝ → ℝ) (cocompact ℝ) atTop).congr'
    filter_upwards [] with x
    simp only [Complex.norm_real]
  have h := cauchy_tendsto_zero (hφ.continuous hα0).continuousOn hn
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (1 : ℝ))] with x hx
  exact (cauchyExtension_ofReal_exterior hφ hα0 hα1 hodd hzero (by simpa using hx)).symm

/-- The extension to the actual one-point compactification is continuous. -/
theorem cauchyCompactifiedBoundary_continuous {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) :
    Continuous (cauchyCompactifiedBoundary φ) := by
  apply (OnePoint.continuous_iff _).2
  exact ⟨cauchy_boundary_tendsto_zero hφ hα0 hα1 hodd hzero,
    (cauchy_boundary_contDiff_one hφ hα0 hα1 hodd hzero).continuous⟩

/-- No boundary points are identified, including the point at infinity. -/
theorem cauchyCompactifiedBoundary_injective {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    Function.Injective (cauchyCompactifiedBoundary φ) := by
  intro x y hxy
  induction x using OnePoint.rec with
  | infty =>
      induction y using OnePoint.rec with
      | infty => rfl
      | coe y =>
          exact False.elim (cauchy_boundary_ne_zero hφ hα0 hα1 hodd hzero hpos y hxy.symm)
  | coe x =>
      induction y using OnePoint.rec with
      | infty =>
          exact False.elim (cauchy_boundary_ne_zero hφ hα0 hα1 hodd hzero hpos x hxy)
      | coe y =>
          exact congrArg (fun t : ℝ => (t : OnePoint ℝ))
            (cauchy_boundary_injective hφ hα0 hα1 hodd hzero hpos hxy)

/-- The range of the actual compactified boundary map is exactly the
frontier of the actual Cauchy image. -/
theorem range_cauchyCompactifiedBoundary {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    range (cauchyCompactifiedBoundary φ) = frontier (cauchyImage φ) := by
  rw [frontier_cauchyImage_eq (hφ.continuous hα0) hodd hzero hpos]
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    induction x using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe x => exact Or.inl ⟨x, rfl⟩
  · rintro (⟨x, rfl⟩ | hz)
    · exact ⟨(x : OnePoint ℝ), rfl⟩
    · exact ⟨∞, (mem_singleton_iff.1 hz).symm⟩

/-- The complete actual boundary map is a closed embedding of the
one-point compactified parameter line. -/
theorem cauchyCompactifiedBoundary_isClosedEmbedding {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    Topology.IsClosedEmbedding (cauchyCompactifiedBoundary φ) :=
  (cauchyCompactifiedBoundary_continuous hφ hα0 hα1 hodd hzero).isClosedEmbedding
    (cauchyCompactifiedBoundary_injective hφ hα0 hα1 hodd hzero hpos)

/-- The constructed compactified real boundary is homeomorphic to the
actual image frontier, with the homeomorphism given by the actual Cauchy
boundary values and zero at infinity. -/
def cauchyBoundaryHomeomorph {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    OnePoint ℝ ≃ₜ frontier (cauchyImage φ) :=
  (cauchyCompactifiedBoundary_isClosedEmbedding hφ hα0 hα1 hodd hzero hpos).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_cauchyCompactifiedBoundary hφ hα0 hodd hzero hpos))

end Torsion.Spectral

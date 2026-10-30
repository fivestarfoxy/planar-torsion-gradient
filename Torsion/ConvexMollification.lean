module

public import Torsion.Definitions
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Convex.Function

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Smooth convex approximation by actual normalized bump convolution

All functions here are the actual Lebesgue convolutions in the pinned
library. Positivity of the mollifier preserves convexity, and a global
Lipschitz modulus gives a uniform approximation bound.
-/

noncomputable section
open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology Convolution ContDiff NNReal

namespace Torsion

/-- The genuine normalized mollification on the physical plane. -/
def convexMollification (f : Plane → ℝ) (φ : ContDiffBump (0 : Plane)) : Plane → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] f

theorem convexMollification_contDiff {f : Plane → ℝ} (hf : Continuous f)
    (φ : ContDiffBump (0 : Plane)) : ContDiff ℝ ∞ (convexMollification f φ) := by
  exact φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hf.locallyIntegrable

/-- Averaging translations against the actual nonnegative normalized bump
preserves convexity. -/
theorem convexMollification_convexOn {f : Plane → ℝ} (hf : Continuous f)
    (hc : ConvexOn ℝ univ f) (φ : ContDiffBump (0 : Plane)) :
    ConvexOn ℝ univ (convexMollification f φ) := by
  have hi (x : Plane) : Integrable (fun t => φ.normed volume t * f (x - t)) volume := by
    exact φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) φ.continuous_normed.locallyIntegrable hf x
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change (∫ t, φ.normed volume t * f (a • x + b • y - t)) ≤
    a * (∫ t, φ.normed volume t * f (x - t)) +
      b * (∫ t, φ.normed volume t * f (y - t))
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hi x).const_mul a)
    ((hi y).const_mul b)]
  apply integral_mono (hi _) (((hi x).const_mul a).add ((hi y).const_mul b))
  intro t
  have he : a • x + b • y - t = a • (x - t) + b • (y - t) := by
    calc
      _ = a • x + b • y - (a + b) • t := by rw [hab, one_smul]
      _ = _ := by rw [add_smul, smul_sub, smul_sub]; abel
  change φ.normed volume t * f (a • x + b • y - t) ≤
    a * (φ.normed volume t * f (x - t)) + b * (φ.normed volume t * f (y - t))
  rw [he]
  have h := mul_le_mul_of_nonneg_left (hc.2 (mem_univ (x - t)) (mem_univ (y - t)) ha hb hab)
    (φ.nonneg_normed (μ := volume) t)
  simp only [smul_eq_mul] at h
  nlinarith

/-- A Lipschitz function and its actual normalized mollification differ
uniformly by at most the Lipschitz constant times the bump radius. -/
theorem convexMollification_dist_le {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : Plane)) (x : Plane) :
    dist (convexMollification f φ x) (f x) ≤ (K : ℝ) * φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left
    (show dist y x ≤ φ.rOut from hy.le) K.coe_nonneg)

/-- Every globally Lipschitz convex real function on the physical plane has
an actual globally smooth convex uniform approximation at any accuracy. -/
theorem exists_contDiff_convex_uniform_approximation {f : Plane → ℝ}
    (hc : ConvexOn ℝ univ f) {K : ℝ≥0} (hf : LipschitzWith K f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Plane → ℝ, ContDiff ℝ ∞ g ∧ ConvexOn ℝ univ g ∧
      ∀ x, |g x - f x| ≤ ε := by
  let ρ : ℝ := ε / ((K : ℝ) + 1)
  have hρ : 0 < ρ := div_pos hε (by positivity)
  let φ : ContDiffBump (0 : Plane) := ⟨ρ / 2, ρ, half_pos hρ, by linarith⟩
  refine ⟨convexMollification f φ, convexMollification_contDiff hf.continuous φ,
    convexMollification_convexOn hf.continuous hc φ, ?_⟩
  intro x
  have h := convexMollification_dist_le hf φ x
  rw [Real.dist_eq] at h
  apply h.trans
  change (K : ℝ) * (ε / ((K : ℝ) + 1)) ≤ ε
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < (K : ℝ) + 1)).mpr
  nlinarith

end Torsion

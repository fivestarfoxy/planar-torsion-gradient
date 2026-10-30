import Torsion.RestrictedSpectralIntervalHolder
import Torsion.CauchyTransformHeightDerivative
import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder regularity of the actual integrated spectral profile

Only square integrability of the original datum is needed: its primitive
has a square-root modulus. The clamped absolute-value endpoint preserves
that modulus globally, including the zero exterior values.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace Torsion.Spectral

private theorem clamped_abs_lipschitz :
    LipschitzWith 1 (fun x : ℝ => min |x| 1) := by
  apply LipschitzWith.min_const
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y

/-- The actual height difference obeys a square-root modulus solely from
square integrability of its datum. -/
theorem height_sub_sq_le {φ : ℝ → ℝ} (hφ : MemLp φ 2 volume) (x y : ℝ) :
    (height φ x - height φ y) ^ 2 ≤
      (∫ s : ℝ, φ s ^ 2) * |x - y| := by
  let a := min |x| 1
  let b := min |y| 1
  have hsub : height φ x - height φ y = ∫ s in a..b, φ s := by
    rw [height_eq_clamped_integral, height_eq_clamped_integral]
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hφ.intervalIntegrable_of_two a b) (hφ.intervalIntegrable_of_two b 1)
    dsimp only [a, b] at *
    linarith
  have hM : 0 ≤ ∫ s : ℝ, φ s ^ 2 := integral_nonneg fun s => sq_nonneg _
  have hdist : |b - a| ≤ |x - y| := by
    have h := clamped_abs_lipschitz.dist_le_mul x y
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_comm, a, b] using h
  rw [hsub]
  exact (hφ.intervalIntegral_sq_le a b).trans (mul_le_mul_of_nonneg_left hdist hM)

/-- Quantitative global square-root modulus for the original height. -/
theorem height_abs_sub_le {φ : ℝ → ℝ} (hφ : MemLp φ 2 volume) (x y : ℝ) :
    |height φ x - height φ y| ≤
      Real.sqrt (∫ s : ℝ, φ s ^ 2) * Real.sqrt |x - y| := by
  have h := height_sub_sq_le hφ x y
  have hM : 0 ≤ ∫ s : ℝ, φ s ^ 2 := integral_nonneg fun s => sq_nonneg _
  have hs1 := Real.sq_sqrt hM
  have hs2 := Real.sq_sqrt (abs_nonneg (x - y))
  have heq : (Real.sqrt (∫ s : ℝ, φ s ^ 2) * Real.sqrt |x - y|) ^ 2 =
      (∫ s : ℝ, φ s ^ 2) * |x - y| := by rw [mul_pow, hs1, hs2]
  have hp : 0 ≤ Real.sqrt (∫ s : ℝ, φ s ^ 2) * Real.sqrt |x - y| := by positivity
  nlinarith [sq_abs (height φ x - height φ y)]

/-- The actual integrated profile is globally Hölder with exponent one
half, with its actual L² norm as constant. -/
theorem height_holder_half_of_memLp {φ : ℝ → ℝ} (hφ : MemLp φ 2 volume) :
    HolderWith ⟨Real.sqrt (∫ s : ℝ, φ s ^ 2), Real.sqrt_nonneg _⟩ (1 / 2) (height φ) := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity)]
  rw [← ENNReal.ofReal_coe_nnreal]
  simp only [NNReal.coe_mk]
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    ← Real.sqrt_eq_rpow] using height_abs_sub_le hφ x y

/-- No pointwise continuity of the datum is required for continuity of
its integrated, zero-extended height. -/
theorem height_continuous_of_memLp {φ : ℝ → ℝ} (hφ : MemLp φ 2 volume) :
    Continuous (height φ) :=
  (height_holder_half_of_memLp hφ).continuous (by norm_num)

/-- Square integrability of the datum gives an integrable actual height. -/
theorem height_integrable_of_memLp {φ : ℝ → ℝ} (hφ : MemLp φ 2 volume) :
    Integrable (height φ) :=
  (height_continuous_of_memLp hφ).integrable_of_hasCompactSupport (height_hasCompactSupport φ)

/-- Every actual restricted form member has a globally one-half Hölder
height. This theorem asserts regularity of the primitive. -/
theorem MemRestrictedFormDomain.height_holder_half {φ : ℝ → ℝ}
    (hφ : MemRestrictedFormDomain φ) :
    ∃ C : ℝ≥0, HolderWith C (1 / 2) (height φ) :=
  ⟨_, height_holder_half_of_memLp hφ.1⟩

/-- Continuity of the actual height throughout the genuine form domain. -/
theorem MemRestrictedFormDomain.height_continuous {φ : ℝ → ℝ}
    (hφ : MemRestrictedFormDomain φ) : Continuous (height φ) :=
  height_continuous_of_memLp hφ.1

/-- Integrability of the actual height throughout the genuine form domain. -/
theorem MemRestrictedFormDomain.height_integrable {φ : ℝ → ℝ}
    (hφ : MemRestrictedFormDomain φ) : Integrable (height φ) :=
  height_integrable_of_memLp hφ.1

/-- A datum of unit L² mass gives the exact global unit square-root
modulus for the actual height. -/
theorem height_abs_sub_le_sqrt_of_integral_sq_eq_one {φ : ℝ → ℝ}
    (hφ : MemLp φ 2 volume) (hunit : (∫ s : ℝ, φ s ^ 2) = 1) (x y : ℝ) :
    |height φ x - height φ y| ≤ Real.sqrt |x - y| := by
  simpa only [hunit, Real.sqrt_one, one_mul] using height_abs_sub_le hφ x y

end Torsion.Spectral

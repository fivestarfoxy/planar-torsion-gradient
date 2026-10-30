import Torsion.CauchyConformalGeometry.BoundaryCurvature
import Torsion.CauchyConformalGeometry.CompactifiedBoundary

/-!
# The concrete supporting functionals of the Cauchy free arc

The linear functional is obtained by rotating the actual tangent. Its
nonvanishing is derived from the proved nonvanishing of the actual tangent.
Reflection and the central and endpoint supporting inequalities are proved
for the actual frontier.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The left normal functional of the actual tangent v-iφ. -/
def cauchySupportFunctional (a b : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℂ →L[ℝ] ℝ :=
  φ t • Complex.reCLM + boundaryVelocity a b φ t • Complex.imCLM

/-- The signed supporting expression based at the actual free-arc point. -/
def cauchySupport (a b : ℝ) (φ : ℝ → ℝ) (t : ℝ) (w : ℂ) : ℝ :=
  cauchySupportFunctional a b φ t w -
    cauchySupportFunctional a b φ t (cauchyExtension φ (t : ℂ))

@[simp] theorem cauchySupportFunctional_apply (a b : ℝ) (φ : ℝ → ℝ) (t : ℝ) (w : ℂ) :
    cauchySupportFunctional a b φ t w =
      φ t * w.re + boundaryVelocity a b φ t * w.im := by
  simp [cauchySupportFunctional]

theorem cauchySupport_eq (a b : ℝ) (φ : ℝ → ℝ) (t : ℝ) (w : ℂ) :
    cauchySupport a b φ t w =
      φ t * (w.re - (cauchyExtension φ (t : ℂ)).re) +
        boundaryVelocity a b φ t * (w.im - height φ t) := by
  simp only [cauchySupport, cauchySupportFunctional_apply, cauchyExtension_ofReal,
    Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  ring

@[simp] theorem cauchySupport_self (a b : ℝ) (φ : ℝ → ℝ) (t : ℝ) :
    cauchySupport a b φ t (cauchyExtension φ (t : ℂ)) = 0 := by
  simp [cauchySupport]

/-- The normal functional cannot vanish, since otherwise both components
of the actual nonvanishing boundary tangent would vanish. -/
theorem cauchySupportFunctional_ne_zero {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : cauchySupportFunctional a b φ t ≠ 0 := by
  intro hnormal
  have hp := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) hnormal
  have hv := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hnormal
  simp only [cauchySupportFunctional_apply, Complex.one_re, Complex.one_im,
    mul_one, mul_zero, add_zero, ContinuousLinearMap.zero_apply] at hp
  simp only [cauchySupportFunctional_apply, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_add, ContinuousLinearMap.zero_apply] at hv
  apply cauchyDerivativeExtension_ne_zero_on_interval ha hφ hα0 hα1 hodd hzero hpos hlinear ht
  rw [cauchy_boundary_tangent_eq hφ hα0 hzero hlinear ht, hp, hv]
  simp

/-- Simultaneously reflecting the base point and the test point preserves
the actual supporting expression. -/
theorem cauchySupport_neg_conj {a b t : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (w : ℂ) :
    cauchySupport a b φ (-t) (-star w) = cauchySupport a b φ t w := by
  rw [cauchySupport_eq, cauchySupport_eq,
    cauchy_boundary_neg_conj hφ hα0 hα1 hodd hzero t, hodd t]
  simp only [Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, neg_neg, boundaryVelocity, height_even φ t]
  ring

/-- Reflection across the imaginary axis preserves the actual frontier. -/
theorem cauchy_frontier_neg_conj_mem {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) {w : ℂ}
    (hw : w ∈ frontier (cauchyImage φ)) : -star w ∈ frontier (cauchyImage φ) := by
  rw [frontier_cauchyImage_eq (hφ.continuous hα0) hodd hzero hpos] at hw ⊢
  rcases hw with ⟨x, rfl⟩ | hw
  · exact Or.inl ⟨-x, cauchy_boundary_neg_conj hφ hα0 hα1 hodd hzero x⟩
  · simp only [mem_singleton_iff] at hw
    simp [hw]

/-- The actual frontier lies in the closed upper half-plane. -/
theorem cauchy_frontier_im_nonneg {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) {w : ℂ}
    (hw : w ∈ frontier (cauchyImage φ)) : 0 ≤ w.im := by
  have hsub : cauchyImage φ ⊆ {z : ℂ | 0 ≤ z.im} := by
    rintro _ ⟨z, hz, rfl⟩
    exact (cauchy_im_pos hφ hpos hz).le
  exact (closure_minimal hsub (isClosed_le continuous_const Complex.continuous_im))
    (frontier_subset_closure hw)

/-- Every actual frontier point is at most as high as the central point. -/
theorem cauchy_frontier_im_le_height_zero {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) {w : ℂ}
    (hw : w ∈ frontier (cauchyImage φ)) : w.im ≤ height φ 0 := by
  rw [frontier_cauchyImage_eq hφ hodd hzero hpos] at hw
  rcases hw with ⟨x, rfl⟩ | hw
  · simpa only [cauchyExtension_ofReal, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add] using
      height_le_at_zero hφ.continuousOn
        (nonneg_on_unitInterval_of_odd_positive hodd hzero hpos) x
  · simp only [mem_singleton_iff] at hw
    rw [hw, Complex.zero_im]
    exact (height_pos hφ.continuousOn hpos (by norm_num : |(0 : ℝ)| < 1)).le

/-- The central horizontal tangent supports the actual entire frontier. -/
theorem cauchySupport_zero_nonneg {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {w : ℂ} (hw : w ∈ frontier (cauchyImage φ)) : 0 ≤ cauchySupport a b φ 0 w := by
  have hφ0 : φ 0 = 0 := by
    have h := hodd 0
    simp only [neg_zero] at h
    linarith
  rw [cauchySupport_eq, hφ0, zero_mul, zero_add]
  have hv := boundaryVelocity_zero_le_negative_half_height ha (hφ.continuous hα0).continuousOn
    hodd hzero hpos
    (moment_identity_of_holder_boundary_equation ha.ne' hφ hα0 hα1 hodd hzero hlinear)
  have hY := height_pos (hφ.continuous hα0).continuousOn hpos (by norm_num : |(0 : ℝ)| < 1)
  apply mul_nonneg_of_nonpos_of_nonpos
  · linarith [mul_pos ha hY]
  · exact sub_nonpos.2 (cauchy_frontier_im_le_height_zero (hφ.continuous hα0) hodd hzero hpos hw)

/-- At the right junction the supporting expression is simply b times
the height above the flat side. -/
theorem cauchySupport_one_eq {a b : ℝ} {φ : ℝ → ℝ}
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (w : ℂ) :
    cauchySupport a b φ 1 w = b * w.im := by
  rw [cauchySupport_eq, hzero 1 (by norm_num)]
  simp [boundaryVelocity, height_zero_of_one_le_abs φ (by norm_num : (1 : ℝ) ≤ |1|)]

/-- The analogous exact formula at the left junction. -/
theorem cauchySupport_neg_one_eq {a b : ℝ} {φ : ℝ → ℝ}
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (w : ℂ) :
    cauchySupport a b φ (-1) w = b * w.im := by
  rw [cauchySupport_eq, hzero (-1) (by norm_num)]
  simp [boundaryVelocity, height_zero_of_one_le_abs φ (by norm_num : (1 : ℝ) ≤ |(-1 : ℝ)|)]

/-- Both junction tangents support the actual entire frontier. -/
theorem cauchySupport_endpoints_nonneg {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {w : ℂ} (hw : w ∈ frontier (cauchyImage φ)) :
    0 ≤ cauchySupport a b φ (-1) w ∧ 0 ≤ cauchySupport a b φ 1 w := by
  rw [cauchySupport_neg_one_eq hzero, cauchySupport_one_eq hzero]
  have hb := (coefficient_pos_and_unique_velocity_zero_of_holder_boundary_equation
    ha hφ hα0 hα1 hodd hzero hpos hlinear).1
  have hwim := cauchy_frontier_im_nonneg (hφ.continuous hα0).continuousOn hpos hw
  exact ⟨mul_nonneg hb.le hwim, mul_nonneg hb.le hwim⟩

end Torsion.Spectral

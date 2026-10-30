module

public import Torsion.CauchyTransformHeightDerivative
public import Torsion.CurvatureFromConcavity
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# The unique zero of the spectral boundary velocity

The velocity is the actual primitive `b - a Y`.  Its strict monotonicity,
negative value at zero and unique interior zero follow from the concrete
moment identity and positivity of the input profile.  This discharges the
zero and velocity-ODE inputs of the strict-curvature theorem.
-/

noncomputable section
open Set MeasureTheory

namespace Torsion.Spectral

/-- The real component of the free-boundary velocity in the linear boundary
equation. -/
def boundaryVelocity (a b : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ := b - a * height φ x

/-- Positivity in the open interval, together with the odd and zero exterior
data, gives nonnegativity at the two endpoints as well. -/
theorem nonneg_on_unitInterval_of_odd_positive {φ : ℝ → ℝ}
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ φ x := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    have hh := hodd 0
    simp only [neg_zero] at hh
    linarith
  by_cases hx1 : x = 1
  · subst x
    rw [hzero 1 (by norm_num)]
  exact (hpos x ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩).le

/-- The integrated height attains its global maximum at the origin. -/
theorem height_le_at_zero {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hφnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ φ x) (x : ℝ) :
    height φ x ≤ height φ 0 := by
  have hzero : height φ 0 = ∫ s in Icc (0 : ℝ) 1, φ s := by
    simp [height]
  rw [hzero]
  by_cases hx : |x| < 1
  · rw [height, if_pos hx]
    apply setIntegral_mono_set hφ.integrableOn_Icc
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact hφnonneg s hs
    · exact ae_of_all _ fun s hs => ⟨(abs_nonneg x).trans hs.1, hs.2⟩
  · rw [height, if_neg hx]
    exact setIntegral_nonneg measurableSet_Icc hφnonneg

/-- The concrete second height moment is at most the maximum height times
the first moment.  This is an actual integral estimate. -/
theorem squareMass_le_height_zero_mul_mass {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hφnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ φ x) :
    squareMass φ ≤ height φ 0 * mass φ := by
  unfold squareMass mass
  calc
    (∫ x in Icc (-1 : ℝ) 1, (height φ x) ^ 2) ≤
        ∫ x in Icc (-1 : ℝ) 1, height φ 0 * height φ x := by
      apply setIntegral_mono_on (squareHeight_integrableOn hφ)
        ((height_integrableOn hφ).const_mul _) measurableSet_Icc
      intro x _
      have hp := height_nonneg hφnonneg x
      have hm := height_le_at_zero hφ hφnonneg x
      nlinarith
    _ = height φ 0 * (∫ x in Icc (-1 : ℝ) 1, height φ x) := integral_const_mul _ _

/-- The genuine primitive has velocity derivative `aφ` everywhere. -/
theorem hasDerivAt_boundaryVelocity {a b : ℝ} {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (x : ℝ) :
    HasDerivAt (boundaryVelocity a b φ) (a * φ x) x := by
  set_option backward.isDefEq.respectTransparency false in
  simpa only [boundaryVelocity, mul_neg, sub_neg_eq_add, zero_add] using!
    (hasDerivAt_const x b).sub ((hasDerivAt_height hφ hodd hzero x).const_mul a)

/-- The actual velocity is strictly increasing on the entire closed
positive interval, including its two endpoints. -/
theorem boundaryVelocity_strictMonoOn {a b : ℝ} {φ : ℝ → ℝ}
    (ha : 0 < a) (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    StrictMonoOn (boundaryVelocity a b φ) (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
    (continuous_const.sub (continuous_const.mul (height_continuous hφ.continuousOn))).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  change 0 < deriv (boundaryVelocity a b φ) x
  rw [(hasDerivAt_boundaryVelocity hφ hodd hzero x).deriv]
  exact mul_pos ha (hpos x hx)

/-- The moment identity and positivity force a strictly negative velocity
at the origin, with the stronger half-height bound from Lemma 5.2. -/
theorem boundaryVelocity_zero_le_negative_half_height {a b : ℝ} {φ : ℝ → ℝ}
    (ha : 0 < a) (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hmoment : a * squareMass φ = 2 * b * mass φ) :
    boundaryVelocity a b φ 0 ≤ -(a * height φ 0) / 2 := by
  have hM := mass_pos hφ hpos
  have hN := squareMass_le_height_zero_mul_mass hφ
    (nonneg_on_unitInterval_of_odd_positive hodd hzero hpos)
  have hb : 2 * b ≤ a * height φ 0 := by
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith [mul_le_mul_of_nonneg_left hN ha.le]
  dsimp [boundaryVelocity]
  linarith

/-- The concrete boundary velocity has exactly one zero in `(0,1)`.
Neither that zero nor the velocity differential equation is assumed. -/
theorem existsUnique_boundaryVelocity_zero {a b : ℝ} {φ : ℝ → ℝ}
    (ha : 0 < a) (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hmoment : a * squareMass φ = 2 * b * mass φ) :
    ∃! x : ℝ, x ∈ Ioo (0 : ℝ) 1 ∧ boundaryVelocity a b φ x = 0 := by
  have hM := mass_pos hφ.continuousOn hpos
  have hN := squareMass_pos hφ.continuousOn hpos
  have hb : 0 < b := by
    have hh : 0 < (2 * b) * mass φ := by rw [← hmoment]; exact mul_pos ha hN
    have hh' : 0 < 2 * b := (mul_pos_iff_of_pos_right hM).mp hh
    linarith
  have hY : 0 < height φ 0 := height_pos hφ.continuousOn hpos (by norm_num)
  have hv0 : boundaryVelocity a b φ 0 < 0 := by
    have hh := boundaryVelocity_zero_le_negative_half_height ha hφ.continuousOn
      hodd hzero hpos hmoment
    have hp := mul_pos ha hY
    linarith
  have hv1 : 0 < boundaryVelocity a b φ 1 := by
    simpa [boundaryVelocity, height_zero_of_one_le_abs φ (by norm_num : (1 : ℝ) ≤ |1|)]
      using hb
  have hvc : Continuous (boundaryVelocity a b φ) :=
    continuous_const.sub (continuous_const.mul (height_continuous hφ.continuousOn))
  obtain ⟨x, hx, hvx⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hvc.continuousOn (show (0 : ℝ) ∈ Icc (boundaryVelocity a b φ 0)
      (boundaryVelocity a b φ 1) from ⟨hv0.le, hv1.le⟩)
  have hx0 : 0 < x := by
    by_contra h
    have heq : x = 0 := le_antisymm (le_of_not_gt h) hx.1
    rw [heq] at hvx
    exact hv0.ne hvx
  have hx1 : x < 1 := by
    by_contra h
    have heq : x = 1 := le_antisymm hx.2 (le_of_not_gt h)
    rw [heq] at hvx
    exact hv1.ne' hvx
  refine ⟨x, ⟨⟨hx0, hx1⟩, hvx⟩, ?_⟩
  intro y hy
  exact (boundaryVelocity_strictMonoOn ha hφ hodd hzero hpos).injOn
    (Ioo_subset_Icc_self hy.1) hx (hy.2.trans hvx.symm)

/-- The strict curvature numerator for the actual boundary velocity follows
from the moment identity and profile concavity.  The interior zero and the
primitive-velocity assumptions in the earlier curvature interface are now
derived rather than supplied. -/
theorem curvature_pos_of_boundary_moments {a b x : ℝ} {φ : ℝ → ℝ}
    (ha : 0 < a) (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hmoment : a * squareMass φ = 2 * b * mass φ)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ y ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ y)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < a * (φ x) ^ 2 - boundaryVelocity a b φ x * deriv φ x := by
  obtain ⟨x₀, hx₀, _⟩ := existsUnique_boundaryVelocity_zero ha hφ hodd hzero hpos hmoment
  exact Curvature.positive_of_concavity_and_velocity ha hc hd hpos
    (fun y _ => hasDerivAt_boundaryVelocity hφ hodd hzero y) hx₀.1 hx hx₀.2

end Torsion.Spectral

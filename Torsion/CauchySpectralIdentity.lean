module

public import Torsion.CauchyTransformBoundaryExtension
public import Torsion.SpectralHolderCalculus
public import Torsion.CauchyQuadraticIdentity
public import Torsion.SpectralBoundaryZeros

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The nonlinear spectral identities from the actual linear Hilbert equation

All Cauchy boundary extensions, their imaginary traces, global boundedness,
holomorphy and infinity decay are constructed in the imported proofs.  The
only spectral boundary equation used here is the linear equation for the
explicit subtracted Hilbert integral.  Its derivation from the restricted
eigenfunction equation remains a separate spectral/distributional step.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace Torsion.Spectral

/-- Lemma 5.2's actual quadratic identity from positive-exponent Hölder
spectral data and the concrete linear Hilbert boundary equation.  There are
no assumed Cauchy extensions, trace theorems, bounds or nonlinear identities
among the inputs. -/
theorem quadratic_identity_of_holder_boundary_equation {a b : ℝ} {φ : ℝ → ℝ}
    {C α : ℝ≥0} (ha : a ≠ 0) (hφ : HolderWith C α φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    ∀ z ∈ upperHalfPlane,
      deriv (auxiliary φ) z = ((b / a : ℝ) : ℂ) * deriv (cauchy φ) z -
        (deriv (cauchy φ) z) ^ 2 / ((2 * a : ℝ) : ℂ) := by
  have hcont := hφ.continuous hα0
  obtain ⟨CYφ, hYφ⟩ := height_mul_exists_holder hφ hα0 hα1 hodd hzero
  apply quadratic_identity_of_boundary_equation (D := cauchyDerivativeExtension φ)
    (E := auxiliaryDerivativeExtension φ) ha hcont.continuousOn hzero
    (cauchyDerivativeExtension_diffContOnCl hφ hα0 hzero).continuousOn
    (auxiliaryDerivativeExtension_diffContOnCl hYφ hα0).continuousOn
    (fun z hz => cauchyDerivativeExtension_eq hcont hodd hzero hz)
    (fun z hz => auxiliaryDerivativeExtension_eq hcont hodd hzero hz)
  · intro x
    simp [cauchyDerivativeExtension_ofReal]
  · intro x
    simp [auxiliaryDerivativeExtension_ofReal]
  · intro x hx
    simp only [cauchyDerivativeExtension_ofReal, Complex.sub_re, Complex.neg_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_self, sub_zero]
    rw [hlinear x hx]
    ring

/-- Comparing the already proved infinity moments gives the actual moment
identity directly from the linear Hilbert equation. -/
theorem moment_identity_of_holder_boundary_equation {a b : ℝ} {φ : ℝ → ℝ}
    {C α : ℝ≥0} (ha : a ≠ 0) (hφ : HolderWith C α φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    a * squareMass φ = 2 * b * mass φ :=
  moment_identity_of_quadratic_identity ha (hφ.continuous hα0).continuousOn
    (quadratic_identity_of_holder_boundary_equation ha hφ hα0 hα1 hodd hzero hlinear)

/-- The abstract positive moment record is now constructed from the actual
Hölder profile and its linear Hilbert boundary equation. -/
def momentsOfHolderBoundaryEquation {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) : Torsion.Moments :=
  momentsOfQuadraticIdentity ha (hφ.continuous hα0).continuousOn hpos
    (quadratic_identity_of_holder_boundary_equation ha.ne' hφ hα0 hα1 hodd hzero hlinear)

/-- The positive coefficient and the unique positive free-arc velocity zero
are consequences of the actual linear boundary equation. -/
theorem coefficient_pos_and_unique_velocity_zero_of_holder_boundary_equation
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    0 < b ∧ ∃! x : ℝ, x ∈ Ioo (0 : ℝ) 1 ∧ boundaryVelocity a b φ x = 0 := by
  have hidentity := quadratic_identity_of_holder_boundary_equation ha.ne'
    hφ hα0 hα1 hodd hzero hlinear
  have hmoment := moment_identity_of_quadratic_identity ha.ne'
    (hφ.continuous hα0).continuousOn hidentity
  exact ⟨coefficient_pos_of_quadratic_identity ha (hφ.continuous hα0).continuousOn
    (mass_pos (hφ.continuous hα0).continuousOn hpos)
    (squareMass_pos (hφ.continuous hα0).continuousOn hpos) hidentity,
    existsUnique_boundaryVelocity_zero ha (hφ.continuous hα0) hodd hzero hpos hmoment⟩

/-- Strict curvature follows from the original Hölder/positivity/concavity
data and the linear Hilbert equation.  A nonlinear moment identity, a zero
of the velocity and a velocity differential equation are all derived. -/
theorem curvature_pos_of_holder_boundary_equation {a b x : ℝ} {φ : ℝ → ℝ}
    {C α : ℝ≥0} (ha : 0 < a) (hφ : HolderWith C α φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ y ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ y)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < a * (φ x) ^ 2 - boundaryVelocity a b φ x * deriv φ x :=
  curvature_pos_of_boundary_moments ha (hφ.continuous hα0) hodd hzero hpos
    (moment_identity_of_holder_boundary_equation ha.ne' hφ hα0 hα1 hodd hzero hlinear)
    hc hd hx

/-- The actual derivative extension has a continuous boundary trace as a
function of the real coordinate. -/
theorem cauchyDerivativeExtension_boundary_continuous {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    Continuous (fun x : ℝ => cauchyDerivativeExtension φ (x : ℂ)) := by
  exact (cauchyDerivativeExtension_diffContOnCl hφ hα0 hzero).continuousOn.comp_continuous
    Complex.continuous_ofReal (fun x => by
      simp [upperHalfPlane, Complex.closure_setOf_lt_im])

/-- The linear equation extends to both support endpoints by actual
continuity.  This provides the positive endpoint derivative `b`. -/
theorem cauchyDerivativeExtension_re_eq_boundaryVelocity {a b : ℝ} {φ : ℝ → ℝ}
    {C α : ℝ≥0} (hφ : HolderWith C α φ) (hα0 : 0 < α)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b) :
    ∀ x ∈ Icc (-1 : ℝ) 1,
      (cauchyDerivativeExtension φ (x : ℂ)).re = boundaryVelocity a b φ x := by
  have heq : EqOn (fun x : ℝ => (cauchyDerivativeExtension φ (x : ℂ)).re)
      (boundaryVelocity a b φ) (Ioo (-1 : ℝ) 1) := by
    intro x hx
    simp [cauchyDerivativeExtension_ofReal, hlinear x hx, boundaryVelocity]
  have hc := heq.closure (Complex.continuous_re.comp
    (cauchyDerivativeExtension_boundary_continuous hφ hα0 hzero))
    (continuous_const.sub (continuous_const.mul
      (height_continuous (hφ.continuous hα0).continuousOn)))
  simpa only [Set.EqOn, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] using! hc

/-- The constructed Cauchy derivative never vanishes on the closed free arc,
including the origin and the two junctions.  This uses the actual negative
central velocity and positive coefficient derived from the moment identity. -/
theorem cauchyDerivativeExtension_ne_zero_on_interval {a b : ℝ} {φ : ℝ → ℝ}
    {C α : ℝ≥0} (ha : 0 < a) (hφ : HolderWith C α φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    cauchyDerivativeExtension φ (x : ℂ) ≠ 0 := by
  have hcont := hφ.continuous hα0
  have hmoment := moment_identity_of_holder_boundary_equation ha.ne' hφ hα0 hα1
    hodd hzero hlinear
  have hb := (coefficient_pos_and_unique_velocity_zero_of_holder_boundary_equation
    ha hφ hα0 hα1 hodd hzero hpos hlinear).1
  have hre := cauchyDerivativeExtension_re_eq_boundaryVelocity hφ hα0 hzero hlinear x hx
  intro hvanish
  have hr : boundaryVelocity a b φ x = 0 := by
    rw [← hre, hvanish]
    rfl
  by_cases hx0 : x = 0
  · subst x
    have hY : 0 < height φ 0 := height_pos hcont.continuousOn hpos (by norm_num)
    have hh := boundaryVelocity_zero_le_negative_half_height ha hcont.continuousOn
      hodd hzero hpos hmoment
    have hp := mul_pos ha hY
    rw [hr] at hh
    linarith
  by_cases hxi : x ∈ Ioo (-1 : ℝ) 1
  · have hφne : φ x ≠ 0 := by
      by_cases hxp : 0 < x
      · exact (hpos x ⟨hxp, hxi.2⟩).ne'
      · have hxn : x < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hx0
        have hp := hpos (-x) (show -x ∈ Ioo (0 : ℝ) 1 from ⟨by linarith, by linarith [hxi.1]⟩)
        have ho := hodd x
        intro heq
        rw [heq, neg_zero] at ho
        exact hp.ne' ho
    have hi := congrArg Complex.im hvanish
    simp [cauchyDerivativeExtension_ofReal] at hi
    exact hφne hi
  · have habs : 1 ≤ |x| := by
      simp only [mem_Ioo, not_and_or, not_lt] at hxi
      rcases hxi with hl | hr
      · exact (neg_le_abs x).trans' (by linarith)
      · exact hr.trans (le_abs_self x)
    have hYzero := height_zero_of_one_le_abs φ habs
    simp [boundaryVelocity, hYzero] at hr
    exact hb.ne' hr

end Torsion.Spectral

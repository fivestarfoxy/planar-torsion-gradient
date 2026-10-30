module

public import Torsion.RestrictedSpectralCorePrimitive
public import Torsion.RestrictedSpectralSymmetry
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual independent directions in the restricted spectral core

An explicit even bump and its odd linear multiple give nonzero admissible
L² directions. In particular every L² vector has a nonzero actual core test
orthogonal to it. This supplies a genuine second direction for variational
spectral selection, rather than assuming the form space has dimension two.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Torsion.Spectral

/-- A fixed smooth bump supported strictly inside the original interval. -/
def restrictedCoreBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def evenCoreDirection (x : ℝ) : ℝ := restrictedCoreBump x

def oddCoreDirection (x : ℝ) : ℝ := x * evenCoreDirection x

theorem evenCoreDirection_isCore : IsCore evenCoreDirection := by
  refine ⟨restrictedCoreBump.contDiff, restrictedCoreBump.hasCompactSupport, ?_⟩
  change tsupport (restrictedCoreBump : ℝ → ℝ) ⊆ Ioo (-1 : ℝ) 1
  rw [restrictedCoreBump.tsupport_eq]
  intro x hx
  have h : |x| ≤ (1 / 2 : ℝ) := by simpa [restrictedCoreBump, Real.dist_eq] using hx
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

theorem oddCoreDirection_isCore : IsCore oddCoreDirection := by
  refine ⟨contDiff_id.mul evenCoreDirection_isCore.1,
    evenCoreDirection_isCore.2.1.mul_left, ?_⟩
  exact tsupport_mul_subset_right.trans evenCoreDirection_isCore.2.2

theorem evenCoreDirection_even : Function.Even evenCoreDirection :=
  restrictedCoreBump.neg

theorem oddCoreDirection_odd : Function.Odd oddCoreDirection := by
  intro x
  simp only [oddCoreDirection, evenCoreDirection_even x]
  ring

@[simp] theorem evenCoreDirection_zero : evenCoreDirection 0 = 1 :=
  restrictedCoreBump.one_of_mem_closedBall (by simp [restrictedCoreBump])

@[simp] theorem oddCoreDirection_zero : oddCoreDirection 0 = 0 := by
  simp [oddCoreDirection]

theorem evenCoreDirection_eighth : evenCoreDirection (1 / 8) = 1 :=
  restrictedCoreBump.one_of_mem_closedBall (by norm_num [restrictedCoreBump, Real.dist_eq])

theorem oddCoreDirection_eighth : oddCoreDirection (1 / 8) = 1 / 8 := by
  rw [oddCoreDirection, evenCoreDirection_eighth, mul_one]

theorem evenCoreDirection_not_ae_zero : ¬ evenCoreDirection =ᵐ[volume] 0 := by
  intro h
  have he := Measure.eq_of_ae_eq h evenCoreDirection_isCore.1.continuous continuous_const
  have h0 := congrFun he 0
  simp at h0

theorem oddCoreDirection_not_ae_zero : ¬ oddCoreDirection =ᵐ[volume] 0 := by
  intro h
  have he := Measure.eq_of_ae_eq h oddCoreDirection_isCore.1.continuous continuous_const
  have h0 := congrFun he (1 / 8)
  norm_num [oddCoreDirection_eighth] at h0

theorem coreDirections_orthogonal :
    (∫ x : ℝ, evenCoreDirection x * oddCoreDirection x) = 0 :=
  integral_mul_eq_zero_of_even_odd evenCoreDirection_even oddCoreDirection_odd

/-- There really is a second admissible direction orthogonal to every
supplied L² vector. Its nonzero property is in the a.e. sense required by
the original spectral definition. -/
theorem exists_core_nonzero_orthogonal {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    ∃ f : ℝ → ℝ, IsCore f ∧ ¬ f =ᵐ[volume] 0 ∧
      (∫ x : ℝ, f x * g x) = 0 := by
  let A : ℝ := ∫ x : ℝ, evenCoreDirection x * g x
  let B : ℝ := ∫ x : ℝ, oddCoreDirection x * g x
  by_cases hA : A = 0
  · exact ⟨evenCoreDirection, evenCoreDirection_isCore,
      evenCoreDirection_not_ae_zero, hA⟩
  let f : ℝ → ℝ := fun x => B * evenCoreDirection x + (-A) * oddCoreDirection x
  have hf : IsCore f :=
    evenCoreDirection_isCore.linear_combination oddCoreDirection_isCore B (-A)
  have hne : ¬ f =ᵐ[volume] 0 := by
    intro h
    have he := Measure.eq_of_ae_eq h hf.1.continuous continuous_const
    have h0 := congrFun he 0
    have hB : B = 0 := by simpa [f] using h0
    have h1 := congrFun he (1 / 8)
    have hmul : (-A) * (1 / 8) = 0 := by
      change B * evenCoreDirection (1 / 8) + (-A) * oddCoreDirection (1 / 8) = 0 at h1
      rw [evenCoreDirection_eighth, oddCoreDirection_eighth, hB, zero_mul, zero_add] at h1
      exact h1
    have : A = 0 := by linarith
    exact hA this
  refine ⟨f, hf, hne, ?_⟩
  have hE : Integrable (fun x : ℝ => evenCoreDirection x * g x) :=
    evenCoreDirection_isCore.memRestrictedFormDomain.1.integrable_mul hg
  have hO : Integrable (fun x : ℝ => oddCoreDirection x * g x) :=
    oddCoreDirection_isCore.memRestrictedFormDomain.1.integrable_mul hg
  calc
    (∫ x : ℝ, f x * g x) = ∫ x : ℝ,
        B * (evenCoreDirection x * g x) + (-A) * (oddCoreDirection x * g x) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [f]; ring
    _ = B * A + (-A) * B := by
      rw [integral_add (hE.const_mul B) (hO.const_mul (-A)),
        integral_const_mul, integral_const_mul]
    _ = 0 := by ring

end Torsion.Spectral

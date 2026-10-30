module

public import Torsion.RestrictedSpectralReflectionOperator
public import Torsion.RestrictedSpectralEigenpairs

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# An actual least odd restricted eigenpair

The odd L² subspace is the closed kernel of reflection plus the identity.
The actual restricted resolvent preserves it. Compact positive spectral
selection in that subspace yields an actual weak eigenfunction, with a
pointwise odd zero-exterior representative and its odd variational bound.
This construction does not identify the least odd eigenpair with the
second unrestricted eigenpair.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral.RestrictedHilbert

/-- The actual closed odd subspace of real L². -/
def oddSpace : Submodule ℝ ValueL2 :=
  LinearMap.ker (reflection + ContinuousLinearMap.id ℝ ValueL2).toLinearMap

theorem isClosed_oddSpace : IsClosed (oddSpace : Set ValueL2) :=
  ContinuousLinearMap.isClosed_ker (reflection + ContinuousLinearMap.id ℝ ValueL2)

instance : CompleteSpace oddSpace := isClosed_oddSpace.completeSpace_coe

/-- Oddness as an L² class is precisely the negative reflection equation. -/
theorem mem_oddSpace_iff (u : ValueL2) : u ∈ oddSpace ↔ reflection u = -u := by
  change (reflection + ContinuousLinearMap.id ℝ ValueL2) u = 0 ↔ _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    add_eq_zero_iff_eq_neg]

/-- A pointwise odd L² function determines an element of the actual odd
subspace, independently of the representative chosen by `toLp`. -/
theorem mem_oddSpace_of_odd {φ : ℝ → ℝ} (hφ : MemLp φ 2 volume)
    (hodd : Function.Odd φ) : hφ.toLp φ ∈ oddSpace := by
  exact (mem_oddSpace_iff _).mpr (reflection_of_odd hφ hodd)

/-- Members of the odd class satisfy the actual odd relation almost
everywhere, with respect to real Lebesgue measure. -/
theorem oddSpace_ae {u : ValueL2} (hu : u ∈ oddSpace) :
    (fun x : ℝ => u (-x)) =ᵐ[volume] fun x => -u x := by
  have hS := reflection_ae u
  rw [(mem_oddSpace_iff u).mp hu] at hS
  filter_upwards [hS, Lp.coeFn_neg u] with x hx hneg
  exact hx.symm.trans hneg

/-- Reflection commutation proves actual invariance of the closed odd
subspace for the original resolvent. -/
theorem oddSpace_invariant : ∀ u ∈ oddSpace, resolvent u ∈ oddSpace := by
  intro u hu
  apply (mem_oddSpace_iff _).mpr
  rw [← resolvent_reflection u, (mem_oddSpace_iff u).mp hu, map_neg]

/-- The actual resolvent restricted to its actual invariant odd subspace. -/
def oddResolventLinear : oddSpace →ₗ[ℝ] oddSpace :=
  resolvent.toLinearMap.restrict oddSpace_invariant

theorem oddResolventLinear_isCompactOperator :
    IsCompactOperator (oddResolventLinear : oddSpace → oddSpace) :=
  resolvent_isCompactOperator.restrict' oddSpace_invariant

/-- The bounded odd restriction, obtained from its proved compactness. -/
def oddResolvent : oddSpace →L[ℝ] oddSpace :=
  ContinuousLinearMap.mkOfIsCompactOperator oddResolventLinear_isCompactOperator

@[simp] theorem oddResolvent_coe (u : oddSpace) :
    (oddResolvent u : ValueL2) = resolvent (u : ValueL2) := rfl

theorem oddResolvent_isCompactOperator :
    IsCompactOperator (oddResolvent : oddSpace → oddSpace) :=
  oddResolventLinear_isCompactOperator

theorem oddResolvent_isSelfAdjoint : IsSelfAdjoint oddResolvent := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  exact resolvent_isSymmetric.restrict_invariant oddSpace_invariant

theorem oddResolvent_nonneg (u : oddSpace) :
    0 ≤ oddResolvent.reApplyInnerSelf u := resolvent_nonneg u

/-- An explicit genuine odd compact smooth source proves that the odd
restriction is a nonzero operator. -/
theorem oddResolvent_ne_zero : oddResolvent ≠ 0 := by
  let f : ValueL2 := oddCoreDirection_isCore.memLp_value.toLp oddCoreDirection
  have hfodd : f ∈ oddSpace :=
    mem_oddSpace_of_odd oddCoreDirection_isCore.memLp_value oddCoreDirection_odd
  let fV : oddSpace := ⟨f, hfodd⟩
  intro hzero
  have hz : oddResolvent fV = 0 := by simp [hzero]
  have h := congrArg (fun z : oddSpace => (z : ValueL2)) hz
  exact (resolvent_core_ne_zero oddCoreDirection_isCore oddCoreDirection_not_ae_zero) h

/-- An explicit pointwise odd representative with the original zero
exterior convention. -/
def oddZeroRepresentative (u : ValueL2) (x : ℝ) : ℝ :=
  if |x| < 1 then (u x - u (-x)) / 2 else 0

theorem oddZeroRepresentative_odd (u : ValueL2) :
    Function.Odd (oddZeroRepresentative u) := by
  intro x
  by_cases hx : |x| < 1
  · simp only [oddZeroRepresentative, abs_neg, hx, if_pos, neg_neg]
    ring
  · simp only [oddZeroRepresentative, abs_neg, hx, if_false, neg_zero]

theorem oddZeroRepresentative_zero_exterior (u : ValueL2) {x : ℝ}
    (hx : 1 ≤ |x|) : oddZeroRepresentative u x = 0 := by
  simp only [oddZeroRepresentative, not_lt.mpr hx, if_false]

/-- For an actual odd form-domain class, the explicit odd zero-exterior
representative preserves its actual L² equivalence class. -/
theorem oddZeroRepresentative_ae {u : ValueL2} (hu : u ∈ oddSpace)
    (hform : MemRestrictedFormDomain (u : ℝ → ℝ)) :
    oddZeroRepresentative u =ᵐ[volume] (u : ℝ → ℝ) := by
  filter_upwards [oddSpace_ae hu, hform.2.2.1] with x hx hzero
  by_cases hxi : |x| < 1
  · simp only [oddZeroRepresentative, hxi, if_pos, hx]
    ring
  · have hnot : x ∉ Ioo (-1 : ℝ) 1 := by
      simpa only [mem_Ioo, ← abs_lt] using hxi
    simp only [oddZeroRepresentative, hxi, if_false]
    exact (hzero hnot).symm

end Torsion.Spectral.RestrictedHilbert

namespace Torsion.Spectral

/-- The original restricted problem has an actual normalized least odd
weak eigenpair. The profile is pointwise odd and globally zero outside
the interval. The comparison is against every original odd admissible
function; no identification with the second unrestricted eigenpair is
claimed. -/
theorem exists_least_odd_restricted_eigenpair :
    ∃ a : ℝ, 0 < a ∧ ∃ φ : ℝ → ℝ,
      IsRestrictedEigenfunction a φ ∧ Function.Odd φ ∧
      (∀ x : ℝ, 1 ≤ |x| → φ x = 0) ∧
      (∫ x : ℝ, (φ x) ^ 2) = 1 ∧
      (∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ → Function.Odd ψ →
        a * (∫ x : ℝ, (ψ x) ^ 2) ≤ energy ψ ψ) := by
  obtain ⟨μ, hμ, v, hv, he, hb⟩ :=
    Torsion.CompactSelfAdjoint.exists_positive_max_eigenpair
      RestrictedHilbert.oddResolvent RestrictedHilbert.oddResolvent_isSelfAdjoint
      RestrictedHilbert.oddResolvent_isCompactOperator
      RestrictedHilbert.oddResolvent_ne_zero RestrictedHilbert.oddResolvent_nonneg
  have he' : RestrictedHilbert.resolvent (v : RestrictedHilbert.ValueL2) =
      μ • (v : RestrictedHilbert.ValueL2) :=
    congrArg (fun z : RestrictedHilbert.oddSpace => (z : RestrictedHilbert.ValueL2)) he
  have hvne : (v : RestrictedHilbert.ValueL2) ≠ 0 := by
    intro hzero
    have hv0 : v = 0 := Subtype.ext hzero
    simp [hv0] at hv
  have hE := RestrictedHilbert.isRestrictedEigenfunction_of_resolvent_eigenvector
    hμ.ne' hvne he'
  let φ : ℝ → ℝ := RestrictedHilbert.oddZeroRepresentative (v : RestrictedHilbert.ValueL2)
  have hae : φ =ᵐ[volume] (v : ℝ → ℝ) :=
    RestrictedHilbert.oddZeroRepresentative_ae v.property hE.1
  refine ⟨1 / μ, one_div_pos.mpr hμ, φ, hE.congr_ae hae.symm,
    RestrictedHilbert.oddZeroRepresentative_odd _,
    (fun x hx => RestrictedHilbert.oddZeroRepresentative_zero_exterior _ hx), ?_, ?_⟩
  · calc
      (∫ x : ℝ, (φ x) ^ 2) = ∫ x : ℝ, ((v : RestrictedHilbert.ValueL2) x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hae] with x hx
        rw [hx]
      _ = 1 := by
        rw [integral_sq_eq_norm_toLp_sq (Lp.memLp (v : RestrictedHilbert.ValueL2)),
          Lp.toLp_coeFn]
        change ‖v‖ ^ 2 = 1
        rw [hv]
        norm_num
  · intro ψ hψ hodd
    have hψodd := RestrictedHilbert.mem_oddSpace_of_odd hψ.1 hodd
    have hbound := Torsion.CompactSelfAdjoint.quadratic_bound_of_rayleigh_bound
      RestrictedHilbert.oddResolvent hb (⟨hψ.1.toLp ψ, hψodd⟩ : RestrictedHilbert.oddSpace)
    exact hψ.energy_ge_of_resolvent_quadratic_bound_at hμ hbound

end Torsion.Spectral

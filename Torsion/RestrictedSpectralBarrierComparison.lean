module

public import Torsion.RestrictedSpectralSmallSupport

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Barrier comparison for the original restricted weak eigenfunction

A genuine weak barrier with constant right-hand side dominates an actual
weak eigenfunction once it dominates outside a sufficiently short interval
and its value is small enough inside that interval. The proof uses only
the original concrete form and its proved positive-part admission.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- Local comparison against an admitted actual barrier satisfying
`L b = 1`, including the eigenvalue's zeroth-order term. -/
theorem IsRestrictedEigenfunction.le_mul_of_small_support_barrier
    {a : ℝ} {φ b : ℝ → ℝ} (hEig : IsRestrictedEigenfunction a φ)
    (hb : MemRestrictedFormDomain b)
    (hbarrier : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      energy b ψ = ∫ x : ℝ, ψ x)
    {l r C : ℝ} (hC : 0 ≤ C) (hlr : l < r)
    (hsmall : a < Real.pi / (4 * (r - l)))
    (houtside : ∀ᵐ x : ℝ, x ∉ Icc l r → φ x ≤ C * b x)
    (hbsmall : ∀ x ∈ Icc l r, a * b x ≤ 1) :
    ∀ᵐ x : ℝ, φ x ≤ C * b x := by
  let d : ℝ → ℝ := fun x => φ x - C * b x
  let p : ℝ → ℝ := fun x => Max.max (d x) 0
  have hd : MemRestrictedFormDomain d := hEig.1.sub (hb.const_mul C)
  have hp : MemRestrictedFormDomain p := hd.pos_part
  have hzero : ∀ᵐ x : ℝ, x ∉ Icc l r → Max.max (d x) 0 = 0 := by
    filter_upwards [houtside] with x hx hout
    exact max_eq_right (sub_nonpos.mpr (hx hout))
  have hpoint (x : ℝ) (hx : x ∈ Icc l r) :
      a * (φ x * p x) - C * p x ≤ a * (p x ^ 2) := by
    have hmul : d x * p x = p x ^ 2 := by
      dsimp only [p]
      rcases le_total (d x) 0 with h | h
      · rw [max_eq_right h]; ring
      · rw [max_eq_left h]; ring
    have hnonpos : C * (a * b x - 1) * p x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hC (sub_nonpos.mpr (hbsmall x hx))) (le_max_right _ _)
    have heq : a * (φ x * p x) - C * p x - a * (p x ^ 2) =
        C * (a * b x - 1) * p x := by
      have h := hmul
      dsimp only [d] at h
      calc
        _ = a * ((φ x - C * b x) * p x - p x ^ 2) + C * (a * b x - 1) * p x := by ring
        _ = _ := by rw [h, sub_self, mul_zero, zero_add]
    linarith
  have hpointAE : ∀ᵐ x : ℝ, a * (φ x * p x) - C * p x ≤ a * (p x ^ 2) := by
    filter_upwards [houtside] with x hx
    by_cases hxin : x ∈ Icc l r
    · exact hpoint x hxin
    · have hpzero : p x = 0 := max_eq_right (sub_nonpos.mpr (hx hxin))
      simp only [hpzero, mul_zero, sub_self, zero_pow (by norm_num : 2 ≠ 0), le_refl]
  have hlefti : Integrable (fun x => a * (φ x * p x) - C * p x) :=
    ((hEig.1.1.integrable_mul hp.1).const_mul a).sub (hp.integrable.const_mul C)
  have hrighti : Integrable (fun x => a * (p x ^ 2)) := hp.1.integrable_sq.const_mul a
  have hI := integral_mono_ae hlefti hrighti hpointAE
  have hIsub : (∫ x : ℝ, a * (φ x * p x) - C * p x) =
      a * (∫ x : ℝ, φ x * p x) - C * ∫ x : ℝ, p x := by
    calc
      _ = (∫ x : ℝ, a * (φ x * p x)) - ∫ x : ℝ, C * p x :=
        integral_sub ((hEig.1.1.integrable_mul hp.1).const_mul a) (hp.integrable.const_mul C)
      _ = _ := by rw [integral_const_mul, integral_const_mul]
  rw [hIsub, integral_const_mul] at hI
  have hdEq : d = fun x => φ x + (-C) * b x := by funext x; dsimp only [d]; ring
  have htest : energy d p ≤ a * ∫ x : ℝ, p x ^ 2 := by
    rw [hdEq, energy_add_left hEig.1.integrable (hb.integrable.const_mul (-C)) hp.integrable
      hEig.1.2.1 (hb.2.1.const_mul hb.integrable (-C)) hp.2.1,
      energy_const_mul_left, hEig.2.2 p hp, hbarrier p hp]
    linarith
  have hn := hd.nonpos_of_small_support_subsolution hlr hsmall hzero htest
  filter_upwards [hn] with x hx
  exact sub_nonpos.mp hx

end Torsion.Spectral

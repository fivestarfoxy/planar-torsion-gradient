module

public import Torsion.RestrictedSpectralOddGap

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Quantitative odd-fold gap on compact positive rectangles

The paired-kernel coefficient has an explicit positive lower bound away
from zero. A small downward perturbation at a zero of f then creates a
linear-sized folding gap against a positive part of f. All estimates are
ordinary scalar inequalities for the actual paired kernel.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- A uniform positive lower bound for the odd paired coefficient on a
compact positive rectangle, off its diagonal. -/
theorem oddAbsGap_coefficient_ge {r R x y : ℝ} (hr : 0 < r)
    (hx : x ∈ Icc r R) (hy : y ∈ Icc r R) (hne : x ≠ y) :
    r ^ 2 / R ^ 4 ≤ 1 / (x - y) ^ 2 - 1 / (x + y) ^ 2 := by
  have hx0 : 0 < x := hr.trans_le hx.1
  have hy0 : 0 < y := hr.trans_le hy.1
  have hR : 0 < R := hx0.trans_le hx.2
  have hA : 0 < (x - y) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hB : 0 < (x + y) ^ 2 := sq_pos_of_pos (add_pos hx0 hy0)
  have hxy : r ^ 2 ≤ x * y := by
    simpa only [pow_two] using mul_le_mul hx.1 hy.1 hr.le hx0.le
  have hAup : (x - y) ^ 2 ≤ R ^ 2 := by
    have hdiff : |x - y| ≤ R := abs_le.2 ⟨by linarith [hy.2], by linarith [hx.2]⟩
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x - y)) hdiff 2
  have hBup : (x + y) ^ 2 ≤ 4 * R ^ 2 := by
    have hsum : x + y ≤ 2 * R := by linarith [hx.2, hy.2]
    have hsq := pow_le_pow_left₀ (add_pos hx0 hy0).le hsum 2
    nlinarith
  have hden : (x - y) ^ 2 * (x + y) ^ 2 ≤ 4 * R ^ 4 := by
    calc
      _ ≤ R ^ 2 * (4 * R ^ 2) :=
        mul_le_mul hAup hBup hB.le (sq_nonneg R)
      _ = _ := by ring
  have hform : 1 / (x - y) ^ 2 - 1 / (x + y) ^ 2 =
      4 * (x * y) / ((x - y) ^ 2 * (x + y) ^ 2) := by
    field_simp
    ring
  rw [hform]
  apply (div_le_div_iff₀ (pow_pos hR 4) (mul_pos hA hB)).2
  calc
    r ^ 2 * ((x - y) ^ 2 * (x + y) ^ 2) ≤ r ^ 2 * (4 * R ^ 4) :=
      mul_le_mul_of_nonneg_left hden (sq_nonneg r)
    _ = 4 * r ^ 2 * R ^ 4 := by ring
    _ ≤ 4 * (x * y) * R ^ 4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxy (by norm_num))
        (pow_nonneg hR.le 4)

/-- A perturbation that is uniformly negative at a zero of f and remains
uniformly positive at another point produces an explicit linear-sized
odd-fold gap. -/
theorem oddAbsGap_perturbation_lower_bound {f ψ : ℝ → ℝ} {r R x y δ η M t : ℝ}
    (hr : 0 < r) (hx : x ∈ Icc r R) (hy : y ∈ Icc r R) (hne : x ≠ y)
    (hδ : 0 < δ) (hη : 0 < η) (ht : 0 < t)
    (hxzero : f x = 0) (hψx : δ ≤ ψ x) (hfy : η ≤ f y)
    (hψy : |ψ y| ≤ M) (htM : t * M ≤ η / 2) :
    (2 * δ * η * (r ^ 2 / R ^ 4)) * t ≤ oddAbsGap (fun z => f z - t * ψ z) x y := by
  have hR : 0 < R := hr.trans_le (hx.1.trans hx.2)
  have hux : f x - t * ψ x ≤ -(t * δ) := by
    rw [hxzero]
    nlinarith [mul_le_mul_of_nonneg_left hψx ht.le]
  have huy : η / 2 ≤ f y - t * ψ y := by
    have hyM : ψ y ≤ M := (le_abs_self _).trans hψy
    nlinarith [mul_le_mul_of_nonneg_left hyM ht.le]
  have hux0 : f x - t * ψ x < 0 := hux.trans_lt (neg_neg_of_pos (mul_pos ht hδ))
  have huy0 : 0 < f y - t * ψ y := (half_pos hη).trans_le huy
  have hprodneg : (f x - t * ψ x) * (f y - t * ψ y) < 0 :=
    mul_neg_of_neg_of_pos hux0 huy0
  have hprod : (f x - t * ψ x) * (f y - t * ψ y) ≤ -(t * δ) * (η / 2) := by
    calc
      _ ≤ -(t * δ) * (f y - t * ψ y) := mul_le_mul_of_nonneg_right hux huy0.le
      _ ≤ _ := mul_le_mul_of_nonpos_left huy (neg_nonpos.2 (mul_pos ht hδ).le)
  have hfactor : t * δ * η ≤
      |(f x - t * ψ x) * (f y - t * ψ y)| -
        (f x - t * ψ x) * (f y - t * ψ y) := by
    rw [abs_of_neg hprodneg]
    nlinarith
  have hcoeff := oddAbsGap_coefficient_ge hr hx hy hne
  have hκ : 0 ≤ r ^ 2 / R ^ 4 := div_nonneg (sq_nonneg r) (pow_nonneg hR.le 4)
  have hgap := mul_le_mul hfactor hcoeff hκ
    (sub_nonneg.2 (le_abs_self ((f x - t * ψ x) * (f y - t * ψ y))))
  unfold oddAbsGap
  dsimp only
  nlinarith [mul_le_mul_of_nonneg_left hgap (by norm_num : (0 : ℝ) ≤ 2)]

end Torsion.Spectral

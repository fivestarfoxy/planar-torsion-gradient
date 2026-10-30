module

public import Torsion.RestrictedSpectralGagliardoKernel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Odd folded contractions for the actual Gagliardo integral

Reflection pairs the same-half and opposite-half kernels. On the positive
quadrant the former coefficient is larger. Every scalar 1-Lipschitz map
fixing zero therefore contracts their paired quadratic form, even though
its odd folding need not be a scalar contraction on the whole line.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- The same-half and reflected-half quadratic kernel on the positive
quadrant. -/
def oddGagliardoPair (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (f x - f y) ^ 2 / (x - y) ^ 2 + (f x + f y) ^ 2 / (x + y) ^ 2

/-- The two positive-quadrant coefficients contract under any actual
scalar 1-Lipschitz map fixing zero. -/
theorem oddGagliardoPair_scalar_le {Φ : ℝ → ℝ}
    (hΦ0 : Φ 0 = 0) (hLip : ∀ u v : ℝ, |Φ u - Φ v| ≤ |u - v|)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) (u v : ℝ) :
    (Φ u - Φ v) ^ 2 / (x - y) ^ 2 + (Φ u + Φ v) ^ 2 / (x + y) ^ 2 ≤
      (u - v) ^ 2 / (x - y) ^ 2 + (u + v) ^ 2 / (x + y) ^ 2 := by
  have hdiff : (Φ u - Φ v) ^ 2 ≤ (u - v) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hLip u v) 2
  have hu : (Φ u) ^ 2 ≤ u ^ 2 := by
    simpa only [hΦ0, sub_zero, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hLip u 0) 2
  have hv : (Φ v) ^ 2 ≤ v ^ 2 := by
    simpa only [hΦ0, sub_zero, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hLip v 0) 2
  have hden : 0 < (x - y) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hAB : 1 / (x + y) ^ 2 ≤ 1 / (x - y) ^ 2 :=
    one_div_le_one_div_of_le hden (by nlinarith [mul_pos hx hy])
  have h1 := mul_le_mul_of_nonneg_left hdiff (sub_nonneg.2 hAB)
  have h2 := mul_le_mul_of_nonneg_left (add_le_add hu hv)
    (show 0 ≤ 2 * (1 / (x + y) ^ 2) by positivity)
  simp only [div_eq_mul_inv, one_div] at *
  nlinarith [h1, h2]

/-- Reflection splits every nonnegative line integral into its two positive
half-line pieces; the omitted origin has zero Lebesgue measure. -/
theorem lintegral_eq_positive_reflection (F : ℝ → ℝ≥0∞) :
    (∫⁻ x : ℝ, F x) = (∫⁻ x in Ioi (0 : ℝ), F x) + ∫⁻ x in Ioi (0 : ℝ), F (-x) := by
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding F (Iio (0 : ℝ))
  have hpre : (fun x : ℝ => -x) ⁻¹' Iio (0 : ℝ) = Ioi 0 := by
    ext x
    simp
  rw [hpre] at hneg
  rw [← lintegral_add_compl F measurableSet_Ioi, compl_Ioi]
  rw [← setLIntegral_congr (Iio_ae_eq_Iic : Iio (0 : ℝ) =ᵐ[volume] Iic 0), hneg]

/-- The paired kernel contracts also on the diagonal, where the same-half
quotient is zero under the original total division convention. -/
theorem oddGagliardoPair_comp_le {Φ : ℝ → ℝ}
    (hΦ0 : Φ 0 = 0) (hLip : ∀ u v : ℝ, |Φ u - Φ v| ≤ |u - v|)
    (f : ℝ → ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    oddGagliardoPair (fun z => Φ (f z)) x y ≤ oddGagliardoPair f x y := by
  by_cases hxy : x = y
  · subst y
    have hu : (Φ (f x)) ^ 2 ≤ (f x) ^ 2 := by
      simpa only [hΦ0, sub_zero, sq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) (hLip (f x) 0) 2
    unfold oddGagliardoPair
    simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, zero_add]
    exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg _)
  · exact oddGagliardoPair_scalar_le hΦ0 hLip hx hy hxy (f x) (f y)

/-- Four-quadrant reflection gives the actual positive-quadrant paired
kernel representation for every measurable odd function. -/
theorem gagliardoEnergy_odd_eq_positive_pair {f : ℝ → ℝ}
    (hf : Measurable f) (hodd : Function.Odd f) :
    gagliardoEnergy f = 2 *
      ∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (oddGagliardoPair f x y) := by
  let K : ℝ → ℝ → ℝ≥0∞ := fun x y =>
    ENNReal.ofReal ((f y - f x) ^ 2 / (y - x) ^ 2)
  have hKm (x : ℝ) : Measurable (K x) := by
    apply Measurable.ennreal_ofReal
    exact ((hf.sub measurable_const).pow_const 2).div
      ((measurable_id.sub measurable_const).pow_const 2)
  have hboth (x y : ℝ) : K (-x) (-y) = K x y := by
    dsimp only [K]
    rw [hodd x, hodd y]
    congr 1
    ring
  have hone (x y : ℝ) : K (-x) y = K x (-y) := by
    dsimp only [K]
    rw [hodd x, hodd y]
    congr 1
    ring
  have hneg (x : ℝ) : (∫⁻ y : ℝ, K (-x) y) = ∫⁻ y : ℝ, K x y := by
    rw [lintegral_eq_positive_reflection (K (-x)), lintegral_eq_positive_reflection (K x)]
    simp_rw [hboth, hone]
    exact add_comm _ _
  have hpair (x y : ℝ) : K x y + K x (-y) = ENNReal.ofReal (oddGagliardoPair f x y) := by
    dsimp only [K, oddGagliardoPair]
    rw [hodd y, ← ENNReal.ofReal_add
      (div_nonneg (sq_nonneg _) (sq_nonneg _)) (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    congr 1
    ring
  have hinner (x : ℝ) : (∫⁻ y : ℝ, K x y) =
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (oddGagliardoPair f x y) := by
    rw [lintegral_eq_positive_reflection (K x), ← lintegral_add_left (hKm x)]
    exact lintegral_congr fun y => hpair x y
  rw [gagliardoEnergy_eq_double hf]
  change (∫⁻ x : ℝ, ∫⁻ y : ℝ, K x y) = _
  rw [lintegral_eq_positive_reflection]
  simp_rw [hneg, hinner]
  exact (two_mul _).symm

/-- Odd folding of any scalar 1-Lipschitz map fixing zero decreases the
actual full real-space energy. Only its concrete positive-half values and
odd reflection are used, so this also applies to flat smooth approximants. -/
theorem gagliardoEnergy_folded_comp_le {f g Φ : ℝ → ℝ}
    (hf : Measurable f) (hodd : Function.Odd f)
    (hg : Measurable g) (hgodd : Function.Odd g)
    (hΦ0 : Φ 0 = 0) (hLip : ∀ u v : ℝ, |Φ u - Φ v| ≤ |u - v|)
    (hpositive : ∀ x : ℝ, 0 < x → g x = Φ (f x)) :
    gagliardoEnergy g ≤ gagliardoEnergy f := by
  rw [gagliardoEnergy_odd_eq_positive_pair hg hgodd,
    gagliardoEnergy_odd_eq_positive_pair hf hodd]
  apply mul_le_mul_right
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  apply ENNReal.ofReal_le_ofReal
  have heq : oddGagliardoPair g x y = oddGagliardoPair (fun z => Φ (f z)) x y := by
    simp only [oddGagliardoPair, hpositive x hx, hpositive y hy]
  rw [heq]
  exact oddGagliardoPair_comp_le hΦ0 hLip f hx hy

end Torsion.Spectral

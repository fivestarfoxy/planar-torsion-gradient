module

public import Torsion.RestrictedSpectralPoincare
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The actual half-energy controls translations in L²

The source-normalized Fourier translation identity and core Parseval give
an explicit `4 |t|` bound. The defining restricted core approximation then
transfers the estimate to every actual form member.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- Translation in space multiplies the actual Fourier integral by its
positive Fourier phase. -/
theorem fourier_comp_add_right (f : ℝ → ℝ) (t ξ : ℝ) :
    fourier (fun x => f (x + t)) ξ =
      Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I) * fourier f ξ := by
  unfold fourier
  calc
    _ = ∫ x : ℝ, Complex.exp (-(((x - t) * ξ : ℝ) : ℂ) * Complex.I) * (f x : ℂ) := by
      simpa only [add_sub_cancel_right] using integral_add_right_eq_self
        (fun x : ℝ => Complex.exp (-(((x - t) * ξ : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) t
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [← mul_assoc, ← Complex.exp_add]
        have he : -(((x - t) * ξ : ℝ) : ℂ) * Complex.I =
            (((t * ξ : ℝ) : ℂ) * Complex.I) + (-((x * ξ : ℝ) : ℂ) * Complex.I) := by
          push_cast
          ring
        rw [he]

/-- A global elementary Fourier phase bound, with no restriction on the
real phase size. -/
theorem norm_exp_real_mul_I_sub_one_le (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ 2 * |t| := by
  have hnorm : ‖(t : ℂ) * Complex.I‖ = |t| := by
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  by_cases ht : |t| ≤ 1
  · simpa only [hnorm] using Complex.norm_exp_sub_one_le (x := (t : ℂ) * Complex.I)
      (by simpa only [hnorm] using ht)
  · have hb := norm_sub_le (Complex.exp ((t : ℂ) * Complex.I)) 1
    have he : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := by simp [Complex.norm_exp]
    rw [he, norm_one] at hb
    linarith [lt_of_not_ge ht]

/-- The square of a Fourier phase difference is controlled by the first
power of its actual frequency, as required by the half-energy. -/
theorem norm_exp_real_mul_I_sub_one_sq_le (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2 ≤ 4 * |t| := by
  by_cases ht : |t| ≤ 1
  · have h := pow_le_pow_left₀ (norm_nonneg _) (norm_exp_real_mul_I_sub_one_le t) 2
    nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht)]
  · have hb := norm_sub_le (Complex.exp ((t : ℂ) * Complex.I)) 1
    have he : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := by simp [Complex.norm_exp]
    rw [he, norm_one] at hb
    have h := pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith [lt_of_not_ge ht]

/-- The actual half-energy bounds translation error for smooth compact
functions, with the source's `2π` factors cancelling exactly. -/
theorem integral_sq_translation_le_of_compact_smooth {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (t : ℝ) :
    (∫ x : ℝ, (f (x + t) - f x) ^ 2) ≤ 4 * |t| * energy f f := by
  let g : ℝ → ℝ := fun x => f (x + t) - f x
  have hft : ContDiff ℝ ∞ (fun x => f (x + t)) :=
    hf.comp (contDiff_id.add contDiff_const)
  have hct : HasCompactSupport (fun x => f (x + t)) :=
    hc.comp_homeomorph (Homeomorph.addRight t)
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  have hfti : Integrable (fun x => f (x + t)) :=
    hft.continuous.integrable_of_hasCompactSupport hct
  have hg : ContDiff ℝ ∞ g := hft.sub hf
  have hgc : HasCompactSupport g := by
    simpa only [g, Pi.sub_apply] using! hct.sub hc
  have hF (ξ : ℝ) : fourier g ξ =
      (Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I) - 1) * fourier f ξ := by
    simp only [g, fourier_sub hfti hfi, Pi.sub_apply, fourier_comp_add_right]
    ring
  have hfe : FiniteEnergy f := finiteEnergy_of_contDiff_hasCompactSupport hf hc
  have hi : (∫ ξ : ℝ, ‖fourier g ξ‖ ^ 2) ≤
      ∫ ξ : ℝ, (4 * |t|) * (|ξ| * ‖fourier f ξ‖ ^ 2) := by
    apply integral_mono (integrable_norm_sq_fourier_of_core hg hgc)
      ((show Integrable (fun ξ : ℝ => |ξ| * ‖fourier f ξ‖ ^ 2) volume from hfe).const_mul _)
    intro ξ
    dsimp only
    rw [hF, norm_mul, mul_pow]
    have h := mul_le_mul_of_nonneg_right (norm_exp_real_mul_I_sub_one_sq_le (t * ξ))
      (sq_nonneg ‖fourier f ξ‖)
    simpa only [abs_mul, mul_assoc] using h
  have hE : (∫ ξ : ℝ, |ξ| * ‖fourier f ξ‖ ^ 2) = (2 * Real.pi) * energy f f := by
    rw [energy_self]
    field_simp [Real.pi_ne_zero]
  rw [integral_norm_sq_fourier_of_core hg hgc, integral_const_mul, hE] at hi
  apply (mul_le_mul_iff_of_pos_left (show 0 < 2 * Real.pi by positivity)).mp
  convert hi using 1
  ring

/-- Translations preserve the real L² seminorm, by actual Haar invariance. -/
theorem eLpNorm_comp_add_right (f : ℝ → ℝ) (t : ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x => f (x + t)) p volume = eLpNorm f p volume := by
  have he := (Homeomorph.addRight t).toMeasurableEquiv.measurableEmbedding
  change eLpNorm (f ∘ (Homeomorph.addRight t).toMeasurableEquiv) p volume = _
  rw [← he.eLpNorm_map_measure]
  change eLpNorm f p (Measure.map (fun x : ℝ => x + t) volume) = _
  rw [(measurePreserving_add_right volume t).map_eq]

/-- The concrete restricted form controls all real translations, after
passing through its defining simultaneous approximants. -/
theorem MemRestrictedFormDomain.integral_sq_translation_le {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (t : ℝ) :
    (∫ x : ℝ, (f (x + t) - f x) ^ 2) ≤ 4 * |t| * energy f f := by
  obtain ⟨v, hv, hL, hE⟩ := hf.2.2.2
  have hvL (n : ℕ) : MemLp (v n) 2 volume :=
    (hv n).1.continuous.memLp_of_hasCompactSupport (hv n).2.1
  have hvI (n : ℕ) : Integrable (v n) :=
    (hv n).1.continuous.integrable_of_hasCompactSupport (hv n).2.1
  have hvE (n : ℕ) : FiniteEnergy (v n) :=
    finiteEnergy_of_contDiff_hasCompactSupport (hv n).1 (hv n).2.1
  have hmp := measurePreserving_add_right (volume : Measure ℝ) t
  have hLt : MemLp (fun x => f (x + t)) 2 volume := hf.1.comp_measurePreserving hmp
  have hvLt (n : ℕ) : MemLp (fun x => v n (x + t)) 2 volume :=
    (hvL n).comp_measurePreserving hmp
  have hlim : Tendsto (fun n => eLpNorm (fun x =>
      (v n (x + t) - v n x) - (f (x + t) - f x)) 2 volume) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hL.add hL)
    · intro n
      exact bot_le
    · intro n
      dsimp only
      have heq : (fun x => (v n (x + t) - v n x) - (f (x + t) - f x)) =
          fun x => (v n (x + t) - f (x + t)) + -(v n x - f x) := by funext x; ring
      rw [heq]
      calc
        _ ≤ eLpNorm (fun x => v n (x + t) - f (x + t)) 2 volume +
            eLpNorm (fun x => -(v n x - f x)) 2 volume :=
          eLpNorm_add_le (by norm_num)
        _ = _ := by
          rw [show eLpNorm (fun x => v n (x + t) - f (x + t)) 2 volume =
              eLpNorm (fun x => v n x - f x) 2 volume from
                eLpNorm_comp_add_right (fun x => v n x - f x) t 2]
          rw [show eLpNorm (fun x => -(v n x - f x)) 2 volume =
              eLpNorm (fun x => v n x - f x) 2 volume from by
                simpa only [Pi.neg_apply] using! eLpNorm_neg (fun x => v n x - f x) 2 volume]
  have hSq := integral_sq_tendsto_of_eLpNorm_sub (hLt.sub hf.1)
    (fun n => (hvLt n).sub (hvL n)) hlim
  have hEn := energy_tendsto_of_difference hf.integrable hvI hf.2.1 hvE hE
  exact le_of_tendsto_of_tendsto hSq (hEn.const_mul (4 * |t|))
    (Eventually.of_forall fun n => integral_sq_translation_le_of_compact_smooth
      (hv n).1 (hv n).2.1 t)

/-- The same translation modulus for the genuine real L² classes. -/
theorem MemRestrictedFormDomain.norm_toLp_translation_sub_sq_le {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (t : ℝ) :
    ‖(hf.1.comp_measurePreserving (measurePreserving_add_right volume t)).toLp
      (fun x => f (x + t)) - hf.1.toLp f‖ ^ 2 ≤ 4 * |t| * energy f f := by
  rw [← MemLp.toLp_sub]
  rw [← integral_sq_eq_norm_toLp_sq]
  exact hf.integral_sq_translation_le t

end Torsion.Spectral

module

public import Torsion.RestrictedSpectralCauchySecondDerivative

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual Cauchy double-pole limits at an interior zero minimum

The local quadratic zero estimate makes the original real double-pole
quotient integrable. Its absolute value dominates the entire vertical
Cauchy double-pole kernel, so ordinary dominated convergence identifies
the boundary value without a principal-value assumption.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- Vertical approach to a real point in the original double-pole Cauchy
integral is dominated by the actual integrable real double-pole quotient. -/
theorem cauchy_doublePole_vertical_tendsto {f : ℝ → ℝ} {x : ℝ}
    (hf : IntegrableOn f (Icc (-1 : ℝ) 1))
    (hquot : IntegrableOn (fun s : ℝ => f s / (x - s) ^ 2) (Icc (-1 : ℝ) 1)) :
    Tendsto (fun y : ℝ => ∫ s in Icc (-1 : ℝ) 1,
      (f s : ℂ) / (((x : ℂ) + (y : ℂ) * Complex.I) - (s : ℂ)) ^ 2)
      (𝓝[>] 0) (𝓝 ((∫ s in Icc (-1 : ℝ) 1, f s / (x - s) ^ 2 : ℝ) : ℂ)) := by
  have hne : ∀ᵐ s : ℝ ∂volume.restrict (Icc (-1 : ℝ) 1), s ≠ x := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  have hfc : Integrable (fun s : ℝ => (f s : ℂ))
      (volume.restrict (Icc (-1 : ℝ) 1)) := Complex.ofRealCLM.integrable_comp hf
  have hmeas (y : ℝ) : AEStronglyMeasurable (fun s : ℝ =>
      (f s : ℂ) / (((x : ℂ) + (y : ℂ) * Complex.I) - (s : ℂ)) ^ 2)
      (volume.restrict (Icc (-1 : ℝ) 1)) :=
    by
      have hd : Continuous (fun s : ℝ =>
          (((x : ℂ) + (y : ℂ) * Complex.I) - (s : ℂ)) ^ 2) := by fun_prop
      simpa only [div_eq_mul_inv] using
        hfc.aestronglyMeasurable.mul hd.measurable.inv.aestronglyMeasurable
  have hbound (y : ℝ) : ∀ᵐ s : ℝ ∂volume.restrict (Icc (-1 : ℝ) 1),
      ‖(f s : ℂ) / (((x : ℂ) + (y : ℂ) * Complex.I) - (s : ℂ)) ^ 2‖ ≤
        ‖f s / (x - s) ^ 2‖ := by
    filter_upwards [hne] with s hs
    have hsq : 0 < (x - s) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hs.symm)
    have hden : (x - s) ^ 2 ≤ ‖((x : ℂ) + (y : ℂ) * Complex.I) - (s : ℂ)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_self, add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, mul_one,
        zero_add, sub_zero]
      nlinarith [sq_nonneg y]
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_div, abs_pow, sq_abs]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hsq hden
  have hlimit : ∀ᵐ s : ℝ ∂volume.restrict (Icc (-1 : ℝ) 1),
      Tendsto (fun y : ℝ => (f s : ℂ) /
        (((x : ℂ) + (y : ℂ) * Complex.I) - (s : ℂ)) ^ 2) (𝓝[>] 0)
        (𝓝 (((f s / (x - s) ^ 2 : ℝ)) : ℂ)) := by
    filter_upwards [hne] with s hs
    have hnot : ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I - (s : ℂ)) ^ 2 ≠ 0 := by
      simp only [Complex.ofReal_zero, zero_mul, add_zero, ← Complex.ofReal_sub,
        ne_eq, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0), Complex.ofReal_eq_zero]
      exact sub_ne_zero.mpr hs.symm
    have hd : Continuous (fun y : ℝ =>
        (((x : ℂ) + (y : ℂ) * Complex.I) - (s : ℂ)) ^ 2) := by fun_prop
    have hc : ContinuousAt (fun y : ℝ => (f s : ℂ) /
        (((x : ℂ) + (y : ℂ) * Complex.I) - (s : ℂ)) ^ 2) 0 :=
      continuousAt_const.div hd.continuousAt hnot
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, ← Complex.ofReal_sub,
      ← Complex.ofReal_pow, ← Complex.ofReal_div] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun s : ℝ => ‖f s / (x - s) ^ 2‖) (Eventually.of_forall hmeas)
    (Eventually.of_forall hbound) hquot.norm hlimit
  simpa only [integral_complex_ofReal] using h

end Torsion.Spectral

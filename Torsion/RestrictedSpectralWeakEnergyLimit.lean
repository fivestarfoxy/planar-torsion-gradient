module

public import Torsion.RestrictedSpectralEnergyContinuity
public import Torsion.RestrictedSpectralFourierWindows
public import Torsion.RestrictedSpectralParseval
public import Torsion.FourierHilbertPairing
public import Torsion.L2Dominated

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Weak vanishing of actual finite-energy Fourier pairings

A sequence with vanishing L¹ norm and bounded actual half-Laplacian energy
pairs to zero against each fixed finite-energy density. No restricted
support or form-domain membership of that sequence is needed.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

private theorem frequencyWindow_inner (u v : Lp ℂ 2 (volume : Measure ℝ)) (R : ℝ) :
    inner (𝕜 := ℝ) (frequencyWindow R u) v = inner (𝕜 := ℝ) u (frequencyWindow R v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [frequencyWindow_ae R u, frequencyWindow_ae R v] with ξ hu hv
  rw [hu, hv]
  by_cases hξ : ξ ∈ Icc (-R) R <;> simp [hξ]

/-- Finite Fourier windows approximate every genuine full-frequency L²
class in its actual norm. -/
theorem norm_sub_frequencyWindow_nat_tendsto (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun N : ℕ => ‖u - frequencyWindow (N : ℝ) u‖) atTop (𝓝 0) := by
  let e : ℕ → ℝ → ℂ := fun N ξ => u ξ - (Icc (-(N : ℝ)) N).indicator u ξ
  have he (N : ℕ) : AEStronglyMeasurable (e N) volume :=
    (Lp.aestronglyMeasurable u).sub ((Lp.aestronglyMeasurable u).indicator measurableSet_Icc)
  have hdom (N : ℕ) : ∀ᵐ ξ : ℝ, ‖‖e N ξ‖ ^ 2‖ ≤ ‖u ξ‖ ^ 2 := by
    exact ae_of_all _ fun ξ => by
      dsimp only [e]
      by_cases hξ : ξ ∈ Icc (-(N : ℝ)) N
      · simp [hξ, sq_nonneg]
      · simp [hξ, Real.norm_of_nonneg (sq_nonneg ‖u ξ‖)]
  have hpoint : ∀ᵐ ξ : ℝ, Tendsto (fun N : ℕ => ‖e N ξ‖ ^ 2) atTop (𝓝 0) := by
    exact ae_of_all _ fun ξ => by
      obtain ⟨N, hN⟩ := exists_nat_gt |ξ|
      have hz : (fun n : ℕ => ‖e n ξ‖ ^ 2) =ᶠ[atTop] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_ge_atTop N] with n hn
        have hn' : |ξ| ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hn)
        have hmem : ξ ∈ Icc (-(n : ℝ)) n := abs_le.1 hn'
        dsimp only [e]
        rw [indicator_of_mem hmem, sub_self, norm_zero]
        norm_num
      exact (tendsto_congr' hz).2 tendsto_const_nhds
  have hsq := tendsto_integral_of_dominated_convergence (fun ξ => ‖u ξ‖ ^ 2)
    (fun N => (he N).norm.pow 2)
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u))
    hdom hpoint
  have hnorm (N : ℕ) : ‖u - frequencyWindow (N : ℝ) u‖ ^ 2 =
      ∫ ξ : ℝ, ‖e N ξ‖ ^ 2 := by
    have h := integral_norm_sq_eq_norm_toLp_sq (Lp.memLp (u - frequencyWindow (N : ℝ) u))
    rw [Lp.toLp_coeFn] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u (frequencyWindow (N : ℝ) u),
      frequencyWindow_ae (N : ℝ) u] with ξ hsub hcut
    simp only [Pi.sub_apply] at hsub
    simp only [hsub, hcut, e]
  have ht : Tendsto (fun N : ℕ => ‖u - frequencyWindow (N : ℝ) u‖ ^ 2)
      atTop (𝓝 0) := by simpa only [hnorm, integral_zero] using hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp ht

/-- A fixed frequency window of the genuine half derivative is controlled
by the actual L¹ norm, with no support condition on the physical density. -/
theorem norm_frequencyWindow_halfDerivative_sq_le {f : ℝ → ℝ}
    (hf : Integrable f) (he : FiniteEnergy f) {R : ℝ} (hR : 0 ≤ R) :
    ‖frequencyWindow R (halfDerivative f hf he)‖ ^ 2 ≤
      2 * R ^ 2 * (∫ x : ℝ, ‖f x‖) ^ 2 := by
  let F := halfDerivative f hf he
  have hnorm := integral_norm_sq_eq_norm_toLp_sq (Lp.memLp (frequencyWindow R F))
  rw [Lp.toLp_coeFn] at hnorm
  rw [← hnorm]
  have hval : (fun ξ : ℝ => ‖frequencyWindow R F ξ‖ ^ 2) =ᵐ[volume]
      (Icc (-R) R).indicator (fun ξ => ‖weightedFourier f ξ‖ ^ 2) := by
    filter_upwards [frequencyWindow_ae R F, halfDerivative_ae f hf he] with ξ hξ hF
    change F ξ = weightedFourier f ξ at hF
    rw [hξ]
    by_cases hI : ξ ∈ Icc (-R) R <;> simp [hI, hF]
  rw [integral_congr_ae hval, integral_indicator measurableSet_Icc]
  have hFint : Integrable (fun ξ : ℝ => ‖weightedFourier f ξ‖ ^ 2) := by
    simpa only [weightedFourier_norm_sq] using he
  have hb : (∫ ξ in Icc (-R) R, ‖weightedFourier f ξ‖ ^ 2) ≤
      ∫ _ξ in Icc (-R) R, R * (∫ x : ℝ, ‖f x‖) ^ 2 := by
    apply setIntegral_mono_on hFint.integrableOn
      ((continuous_const : Continuous (fun _ : ℝ => R * (∫ x : ℝ, ‖f x‖) ^ 2)).integrableOn_Icc)
      measurableSet_Icc
    intro ξ hξ
    rw [weightedFourier_norm_sq]
    exact mul_le_mul (abs_le.2 hξ)
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fourier_le_integral_norm f ξ) 2)
      (sq_nonneg _) hR
  simp only [setIntegral_const, Measure.real, Real.volume_Icc, sub_neg_eq_add,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ R + R by linarith), smul_eq_mul] at hb
  convert hb using 1
  ring

/-- Vanishing L¹ norm makes every fixed Fourier window of the actual half
derivative converge strongly to zero. -/
theorem norm_frequencyWindow_halfDerivative_tendsto_zero
    {w : ℕ → ℝ → ℝ} (hw : ∀ n, Integrable (w n)) (hew : ∀ n, FiniteEnergy (w n))
    (hL : Tendsto (fun n => ∫ x : ℝ, ‖w n x‖) atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n => ‖frequencyWindow R (halfDerivative (w n) (hw n) (hew n))‖)
      atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => ‖frequencyWindow R (halfDerivative (w n) (hw n) (hew n))‖ ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _)
      (fun n => norm_frequencyWindow_halfDerivative_sq_le (hw n) (hew n) hR)
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using (hL.pow 2).const_mul (2 * R ^ 2)
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

/-- Actual weak energy vanishing: L¹ convergence to zero and a uniform
bound on the existing Fourier diagonal energies suffice. The moving
functions need not belong to the restricted form domain. -/
theorem energy_tendsto_zero_of_integral_norm_tendsto_zero_of_bounded_energy
    {f : ℝ → ℝ} {w : ℕ → ℝ → ℝ} {B : ℝ}
    (hf : Integrable f) (hef : FiniteEnergy f)
    (hw : ∀ n, Integrable (w n)) (hew : ∀ n, FiniteEnergy (w n))
    (hL : Tendsto (fun n => ∫ x : ℝ, ‖w n x‖) atTop (𝓝 0))
    (hB : ∀ n, energy (w n) (w n) ≤ B) :
    Tendsto (fun n => energy f (w n)) atTop (𝓝 0) := by
  let F := halfDerivative f hf hef
  let W : ℕ → Lp ℂ 2 (volume : Measure ℝ) := fun n => halfDerivative (w n) (hw n) (hew n)
  have hB0 : 0 ≤ B := (energy_nonneg (w 0)).trans (hB 0)
  let M : ℝ := Real.sqrt ((2 * Real.pi) * B)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hW (n : ℕ) : ‖W n‖ ≤ M := by
    have hE := energy_self_eq_norm_halfDerivative (hw n) (hew n)
    have hEsq : ‖W n‖ ^ 2 ≤ (2 * Real.pi) * B := by
      have h := mul_le_mul_of_nonneg_left (hB n) (show 0 ≤ 2 * Real.pi by positivity)
      rw [hE] at h
      dsimp only [W]
      field_simp at h
      exact h
    exact Real.le_sqrt_of_sq_le hEsq
  have hpair : Tendsto (fun n => inner (𝕜 := ℝ) F (W n)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hsmall := (norm_sub_frequencyWindow_nat_tendsto F).eventually
      (Iio_mem_nhds (show (0 : ℝ) < ε / (2 * (M + 1)) by positivity))
    obtain ⟨N, hN⟩ := hsmall.exists
    have hlow : Tendsto (fun n => inner (𝕜 := ℝ) F (frequencyWindow (N : ℝ) (W n)))
        atTop (𝓝 0) := by
      apply squeeze_zero_norm
      · intro n
        exact norm_inner_le_norm F (frequencyWindow (N : ℝ) (W n))
      · simpa only [mul_zero] using
          (norm_frequencyWindow_halfDerivative_tendsto_zero hw hew hL
            (show (0 : ℝ) ≤ N by positivity)).const_mul ‖F‖
    obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.1 hlow (ε / 2) (half_pos hε)
    refine ⟨n₀, fun n hn => ?_⟩
    have hlowN := hn₀ n hn
    have heq : inner (𝕜 := ℝ) F (W n) =
        inner (𝕜 := ℝ) (F - frequencyWindow (N : ℝ) F) (W n) +
        inner (𝕜 := ℝ) F (frequencyWindow (N : ℝ) (W n)) := by
      rw [inner_sub_left, frequencyWindow_inner]
      ring
    rw [Real.dist_eq, sub_zero] at hlowN ⊢
    rw [heq]
    calc
      _ ≤ |inner (𝕜 := ℝ) (F - frequencyWindow (N : ℝ) F) (W n)| +
          |inner (𝕜 := ℝ) F (frequencyWindow (N : ℝ) (W n))| := abs_add_le _ _
      _ ≤ ‖F - frequencyWindow (N : ℝ) F‖ * M +
          |inner (𝕜 := ℝ) F (frequencyWindow (N : ℝ) (W n))| := by
        apply add_le_add_right
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hW n) (norm_nonneg _))
      _ < ε := by
        have htail : ‖F - frequencyWindow (N : ℝ) F‖ * M < ε / 2 := by
          have h := mul_lt_mul_of_pos_right hN (show 0 < M + 1 by positivity)
          have hc : ε / (2 * (M + 1)) * (M + 1) = ε / 2 := by field_simp; ring
          rw [hc] at h
          nlinarith [norm_nonneg (F - frequencyWindow (N : ℝ) F)]
        linarith
  have h := hpair.const_mul (1 / (2 * Real.pi))
  simpa only [mul_zero, energy_eq_inner_halfDerivative hf (hw _) hef (hew _)] using h

end Torsion.Spectral

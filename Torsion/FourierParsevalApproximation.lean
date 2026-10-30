module

public import Torsion.RestrictedSpectralParseval

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Parseval through arbitrary compact smooth approximants

The support of the approximants may move, as needed for translations and
Lipschitz compositions. Simultaneous actual L¹ and L² convergence identifies
the complete-space Fourier limit with the original integral transform.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

theorem compactSmooth_fourier_memLp {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : MemLp (fourier f) 2 volume :=
  (memLp_two_iff_integrable_sq_norm
    (fourier_continuous (hf.continuous.integrable_of_hasCompactSupport hc)).aestronglyMeasurable).mpr
      (integrable_norm_sq_fourier_of_core hf hc)

/-- The actual integral Fourier transform of a compact smooth function as
its ordinary L² class, with no interval-support requirement. -/
def compactSmoothFourierL2 (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Lp ℂ 2 (volume : Measure ℝ) := (compactSmooth_fourier_memLp hf hc).toLp (fourier f)

theorem compactSmoothFourierL2_ae (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (compactSmoothFourierL2 f hf hc : ℝ → ℂ) =ᵐ[volume] fourier f :=
  (compactSmooth_fourier_memLp hf hc).coeFn_toLp

/-- Parseval gives the exact Fourier distance for arbitrary compact smooth
real functions, including translates of restricted core functions. -/
theorem compactSmoothFourierL2_norm_sub {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ‖compactSmoothFourierL2 f hf hfc - compactSmoothFourierL2 g hg hgc‖ =
      Real.sqrt (2 * Real.pi) *
        ‖(hf.continuous.memLp_of_hasCompactSupport hfc : MemLp f 2 volume).toLp f -
          (hg.continuous.memLp_of_hasCompactSupport hgc : MemLp g 2 volume).toLp g‖ := by
  have hfreq : (∫ ξ : ℝ, ‖fourier f ξ - fourier g ξ‖ ^ 2) =
      ‖compactSmoothFourierL2 f hf hfc - compactSmoothFourierL2 g hg hgc‖ ^ 2 := by
    have h := integral_norm_sq_eq_norm_toLp_sq
      ((compactSmooth_fourier_memLp hf hfc).sub (compactSmooth_fourier_memLp hg hgc))
    simpa only [MemLp.toLp_sub, compactSmoothFourierL2, Pi.sub_apply] using! h
  have hval : (∫ x : ℝ, (f x - g x) ^ 2) =
      ‖(hf.continuous.memLp_of_hasCompactSupport hfc : MemLp f 2 volume).toLp f -
        (hg.continuous.memLp_of_hasCompactSupport hgc : MemLp g 2 volume).toLp g‖ ^ 2 := by
    have h := integral_sq_eq_norm_toLp_sq
      ((hf.continuous.memLp_of_hasCompactSupport hfc : MemLp f 2 volume).sub
        (hg.continuous.memLp_of_hasCompactSupport hgc))
    simpa only [MemLp.toLp_sub, Pi.sub_apply] using! h
  have hsubc : HasCompactSupport (fun x => f x - g x) := by
    simpa only [sub_eq_add_neg, Pi.add_def, Function.comp_def] using!
      hfc.add (hgc.comp_left (g := fun t : ℝ => -t) (by simp))
  have hp := integral_norm_sq_fourier_of_core (hf.sub hg) hsubc
  rw [fourier_sub (hf.continuous.integrable_of_hasCompactSupport hfc)
    (hg.continuous.integrable_of_hasCompactSupport hgc)] at hp
  simp only [Pi.sub_apply] at hp
  rw [hfreq, hval] at hp
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact hp

/-- Parseval for an actual L¹∩L² function approximated by arbitrary compact
smooth functions in both norms. Their supports need not stay in `(-1,1)`. -/
theorem fourier_parseval_of_compactSmooth_approximation {f : ℝ → ℝ} {v : ℕ → ℝ → ℝ}
    (hf : MemLp f 2 volume) (hfi : Integrable f)
    (hv : ∀ n, ContDiff ℝ ∞ (v n) ∧ HasCompactSupport (v n))
    (hval : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0))
    (hL1 : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 1 volume) atTop (𝓝 0)) :
    MemLp (fourier f) 2 volume ∧
      (∫ ξ : ℝ, ‖fourier f ξ‖ ^ 2) = (2 * Real.pi) * ∫ x : ℝ, f x ^ 2 := by
  have hvmem (n : ℕ) : MemLp (v n) 2 volume :=
    (hv n).1.continuous.memLp_of_hasCompactSupport (hv n).2
  have hvi (n : ℕ) : Integrable (v n) :=
    (hv n).1.continuous.integrable_of_hasCompactSupport (hv n).2
  let V : ℕ → Lp ℝ 2 (volume : Measure ℝ) := fun n => (hvmem n).toLp (v n)
  let F : ℕ → Lp ℂ 2 (volume : Measure ℝ) := fun n => compactSmoothFourierL2 (v n) (hv n).1 (hv n).2
  have hV : Tendsto V atTop (𝓝 (hf.toLp f)) := by
    apply tendsto_iff_edist_tendsto_0.mpr
    simpa only [V, Lp.edist_toLp_toLp, Pi.sub_def] using hval
  obtain ⟨B, hB0, hB, hBlim⟩ := cauchySeq_iff_le_tendsto_0.mp hV.cauchySeq
  have hFcauchy : CauchySeq F := by
    apply cauchySeq_iff_le_tendsto_0.mpr
    refine ⟨fun n => Real.sqrt (2 * Real.pi) * B n,
      fun n => mul_nonneg (Real.sqrt_nonneg _) (hB0 n), ?_, ?_⟩
    · intro n m N hn hm
      change dist (compactSmoothFourierL2 (v n) (hv n).1 (hv n).2)
        (compactSmoothFourierL2 (v m) (hv m).1 (hv m).2) ≤ _
      rw [dist_eq_norm, compactSmoothFourierL2_norm_sub]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm, V] using hB n m N hn hm) (Real.sqrt_nonneg _)
    · simpa only [mul_zero] using hBlim.const_mul (Real.sqrt (2 * Real.pi))
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hFcauchy
  have hHae : (H : ℝ → ℂ) =ᵐ[volume] fourier f :=
    fourier_ae_eq_of_tendsto_L1 hvi hfi hL1
      (fun n => compactSmoothFourierL2_ae (v n) (hv n).1 (hv n).2) hH
  refine ⟨MemLp.ae_eq hHae (Lp.memLp H), ?_⟩
  have hFnorm (n : ℕ) : (∫ ξ : ℝ, ‖fourier (v n) ξ‖ ^ 2) = ‖F n‖ ^ 2 :=
    integral_norm_sq_eq_norm_toLp_sq (compactSmooth_fourier_memLp (hv n).1 (hv n).2)
  have hHnorm : (∫ ξ : ℝ, ‖fourier f ξ‖ ^ 2) = ‖H‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hHae] with ξ hξ
    simp only [hξ, real_inner_self_eq_norm_sq]
  have hfreqLimit : Tendsto (fun n => ∫ ξ : ℝ, ‖fourier (v n) ξ‖ ^ 2) atTop
      (𝓝 (∫ ξ : ℝ, ‖fourier f ξ‖ ^ 2)) := by
    simpa only [hFnorm, hHnorm] using hH.norm.pow 2
  have hvalueLimit := (integral_sq_tendsto_of_eLpNorm_sub hf hvmem hval).const_mul (2 * Real.pi)
  have heq (n : ℕ) : (∫ ξ : ℝ, ‖fourier (v n) ξ‖ ^ 2) =
      (2 * Real.pi) * ∫ x : ℝ, (v n x) ^ 2 :=
    integral_norm_sq_fourier_of_core (hv n).1 (hv n).2
  exact tendsto_nhds_unique hfreqLimit (hvalueLimit.congr' (Eventually.of_forall fun n => (heq n).symm))

end Torsion.Spectral

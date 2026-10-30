module

public import Torsion.RestrictedSpectralFourierContinuity
public import Torsion.FourierPlancherel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Parseval on the actual restricted form domain

The original compact smooth Fourier transforms satisfy Parseval. Their
L² limits are constructed in the ordinary complete complex L² space and
identified with the actual Fourier integrals by common-support L¹
continuity. This proves Parseval beyond the core, without assuming it.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- The actual unweighted Fourier integral of every core member belongs to
ordinary L². -/
theorem IsCore.fourier_memLp {f : ℝ → ℝ} (hf : IsCore f) :
    MemLp (fourier f) 2 volume :=
  (memLp_two_iff_integrable_sq_norm
    (fourier_continuous hf.memRestrictedFormDomain.integrable).aestronglyMeasurable).mpr
      (integrable_norm_sq_fourier_of_core hf.1 hf.2.1)

/-- The source Fourier integral of a core member as its actual L² class. -/
def fourierCoreL2 (f : ℝ → ℝ) (hf : IsCore f) : Lp ℂ 2 (volume : Measure ℝ) :=
  hf.fourier_memLp.toLp (fourier f)

theorem fourierCoreL2_ae (f : ℝ → ℝ) (hf : IsCore f) :
    (fourierCoreL2 f hf : ℝ → ℂ) =ᵐ[volume] fourier f := hf.fourier_memLp.coeFn_toLp

/-- The actual squared integral is the norm squared of a complex L² class. -/
theorem integral_norm_sq_eq_norm_toLp_sq {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    (∫ x : ℝ, ‖f x‖ ^ 2) = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq]

/-- Parseval gives the exact norm of the difference of two actual core
Fourier L² classes. -/
theorem fourierCoreL2_norm_sub {f g : ℝ → ℝ} (hf : IsCore f) (hg : IsCore g) :
    ‖fourierCoreL2 f hf - fourierCoreL2 g hg‖ = Real.sqrt (2 * Real.pi) *
      ‖hf.memRestrictedFormDomain.1.toLp f - hg.memRestrictedFormDomain.1.toLp g‖ := by
  have hsub : IsCore (fun x => f x - g x) := by
    convert hf.add (hg.const_mul (-1)) using 1
    funext x
    ring
  have hfreq : (∫ ξ : ℝ, ‖fourier f ξ - fourier g ξ‖ ^ 2) =
      ‖fourierCoreL2 f hf - fourierCoreL2 g hg‖ ^ 2 := by
    have h := integral_norm_sq_eq_norm_toLp_sq (hf.fourier_memLp.sub hg.fourier_memLp)
    simpa only [MemLp.toLp_sub, fourierCoreL2, Pi.sub_apply] using h
  have hval : (∫ x : ℝ, (f x - g x) ^ 2) =
      ‖hf.memRestrictedFormDomain.1.toLp f - hg.memRestrictedFormDomain.1.toLp g‖ ^ 2 := by
    have h := integral_sq_eq_norm_toLp_sq (hf.memRestrictedFormDomain.1.sub hg.memRestrictedFormDomain.1)
    simpa only [MemLp.toLp_sub, Pi.sub_apply] using h
  have hparseval := integral_norm_sq_fourier_of_core hsub.1 hsub.2.1
  rw [fourier_sub hf.memRestrictedFormDomain.integrable hg.memRestrictedFormDomain.integrable] at hparseval
  simp only [Pi.sub_apply] at hparseval
  rw [hfreq, hval] at hparseval
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact hparseval

/-- Actual L² convergence of compact smooth restricted approximants gives
an actual Fourier L² limit and the full Parseval identity for that limit. -/
theorem fourier_parseval_of_core_approximation {f : ℝ → ℝ} {v : ℕ → ℝ → ℝ}
    (hf : MemLp f 2 volume) (hv : ∀ n, IsCore (v n))
    (hval : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0)) :
    MemLp (fourier f) 2 volume ∧
      (∫ ξ : ℝ, ‖fourier f ξ‖ ^ 2) = (2 * Real.pi) * ∫ x : ℝ, f x ^ 2 := by
  let V : ℕ → Lp ℝ 2 (volume : Measure ℝ) := fun n =>
    (hv n).memRestrictedFormDomain.1.toLp (v n)
  let F : ℕ → Lp ℂ 2 (volume : Measure ℝ) := fun n => fourierCoreL2 (v n) (hv n)
  have hV : Tendsto V atTop (𝓝 (hf.toLp f)) := by
    apply tendsto_iff_edist_tendsto_0.mpr
    simpa only [V, Lp.edist_toLp_toLp] using hval
  obtain ⟨B, hB0, hB, hBlim⟩ := cauchySeq_iff_le_tendsto_0.mp hV.cauchySeq
  have hFcauchy : CauchySeq F := by
    apply cauchySeq_iff_le_tendsto_0.mpr
    refine ⟨fun n => Real.sqrt (2 * Real.pi) * B n,
      fun n => mul_nonneg (Real.sqrt_nonneg _) (hB0 n), ?_, ?_⟩
    · intro n m N hn hm
      change dist (fourierCoreL2 (v n) (hv n)) (fourierCoreL2 (v m) (hv m)) ≤ _
      rw [dist_eq_norm, fourierCoreL2_norm_sub]
      exact mul_le_mul_of_nonneg_left (hB n m N hn hm) (Real.sqrt_nonneg _)
    · simpa only [mul_zero] using hBlim.const_mul (Real.sqrt (2 * Real.pi))
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hFcauchy
  have hHae : (H : ℝ → ℂ) =ᵐ[volume] fourier f :=
    fourier_ae_eq_of_tendsto (fun n => (hv n).memRestrictedFormDomain.1) hf
      (fun n => (hv n).memRestrictedFormDomain.2.2.1) hval
      (fun n => fourierCoreL2_ae (v n) (hv n)) hH
  have hfourier : MemLp (fourier f) 2 volume := MemLp.ae_eq hHae (Lp.memLp H)
  refine ⟨hfourier, ?_⟩
  have hFnorm (n : ℕ) : (∫ ξ : ℝ, ‖fourier (v n) ξ‖ ^ 2) = ‖F n‖ ^ 2 :=
    integral_norm_sq_eq_norm_toLp_sq (hv n).fourier_memLp
  have hHnorm : (∫ ξ : ℝ, ‖fourier f ξ‖ ^ 2) = ‖H‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hHae] with ξ hξ
    simp only [hξ, real_inner_self_eq_norm_sq]
  have hfreqLimit : Tendsto (fun n => ∫ ξ : ℝ, ‖fourier (v n) ξ‖ ^ 2) atTop
      (𝓝 (∫ ξ : ℝ, ‖fourier f ξ‖ ^ 2)) := by
    simpa only [hFnorm, hHnorm] using hH.norm.pow 2
  have hvalueLimit := (integral_sq_tendsto_of_eLpNorm_sub hf
    (fun n => (hv n).memRestrictedFormDomain.1) hval).const_mul (2 * Real.pi)
  have heq (n : ℕ) : (∫ ξ : ℝ, ‖fourier (v n) ξ‖ ^ 2) =
      (2 * Real.pi) * ∫ x : ℝ, (v n x) ^ 2 :=
    integral_norm_sq_fourier_of_core (hv n).1 (hv n).2.1
  exact tendsto_nhds_unique hfreqLimit (hvalueLimit.congr' (Eventually.of_forall fun n => (heq n).symm))

/-- Parseval holds for every member of the original concrete restricted
form domain, with the original integral Fourier definition. -/
theorem MemRestrictedFormDomain.fourier_parseval {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) :
    MemLp (fourier f) 2 volume ∧
      (∫ ξ : ℝ, ‖fourier f ξ‖ ^ 2) = (2 * Real.pi) * ∫ x : ℝ, f x ^ 2 := by
  obtain ⟨v, hv, hval, _⟩ := hf.2.2.2
  exact fourier_parseval_of_core_approximation hf.1 hv hval

end Torsion.Spectral

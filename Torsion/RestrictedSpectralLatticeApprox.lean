module

public import Torsion.RestrictedSpectralGagliardo
public import Torsion.SmoothPositivePart
public import Torsion.L2Dominated

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smooth absolute-value approximants for the actual restricted form

The existing flat positive-part primitive produces smooth scalar absolute
value approximations that fix zero and are 1-Lipschitz. Their compositions
preserve the original restricted core and contract its actual Fourier
energy. Joint L² convergence is proved for the concrete approximants.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- A smooth, zero-preserving absolute-value approximation from the
already constructed flat positive-part primitive. -/
def spectralAbsApprox (n : ℕ) (t : ℝ) : ℝ :=
  SmoothPositivePart.approx n t + SmoothPositivePart.approx n (-t)

@[simp] theorem spectralAbsApprox_zero (n : ℕ) : spectralAbsApprox n 0 = 0 := by
  simp [spectralAbsApprox]

theorem spectralAbsApprox_contDiff (n : ℕ) : ContDiff ℝ ∞ (spectralAbsApprox n) :=
  (SmoothPositivePart.approx_contDiff n).add
    ((SmoothPositivePart.approx_contDiff n).comp contDiff_neg)

theorem spectralAbsApprox_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (spectralAbsApprox n)
      (SmoothPositivePart.slope n t - SmoothPositivePart.slope n (-t)) t := by
  convert (SmoothPositivePart.approx_hasDerivAt n t).add
    ((SmoothPositivePart.approx_hasDerivAt n (-t)).comp t (hasDerivAt_neg t)) using 1
  · funext x
    rfl
  · ring

theorem spectralAbsApprox_lipschitz (n : ℕ) : LipschitzWith 1 (spectralAbsApprox n) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (spectralAbsApprox_hasDerivAt n t).differentiableAt)
  intro t
  rw [(spectralAbsApprox_hasDerivAt n t).deriv]
  have hnorm : ‖SmoothPositivePart.slope n t - SmoothPositivePart.slope n (-t)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [SmoothPositivePart.slope_nonneg n t,
      SmoothPositivePart.slope_nonneg n (-t), SmoothPositivePart.slope_le_one n t,
      SmoothPositivePart.slope_le_one n (-t)]
  exact_mod_cast hnorm

theorem spectralAbsApprox_norm_le (n : ℕ) (t : ℝ) : ‖spectralAbsApprox n t‖ ≤ ‖t‖ := by
  simpa only [dist_eq_norm, spectralAbsApprox_zero, sub_zero, NNReal.coe_one, one_mul] using
    (spectralAbsApprox_lipschitz n).dist_le_mul t 0

theorem tendsto_spectralAbsApprox (t : ℝ) :
    Tendsto (fun n => spectralAbsApprox n t) atTop (𝓝 |t|) := by
  have h := (SmoothPositivePart.tendsto_approx t).add (SmoothPositivePart.tendsto_approx (-t))
  have heq : max t 0 + max (-t) 0 = |t| := by
    rcases le_total 0 t with ht | ht
    · simp [max_eq_left ht, max_eq_right (neg_nonpos.2 ht), abs_of_nonneg ht]
    · simp [max_eq_right ht, max_eq_left (neg_nonneg.2 ht), abs_of_nonpos ht]
  simpa only [spectralAbsApprox, heq] using h

/-- Actual restricted core admission of every smooth absolute-value
approximation; in particular its support stays strictly inside the interval. -/
theorem IsCore.spectralAbsApprox {f : ℝ → ℝ} (hf : IsCore f) (n : ℕ) :
    IsCore (fun x => spectralAbsApprox n (f x)) := by
  refine ⟨(spectralAbsApprox_contDiff n).comp hf.1,
    hf.2.1.comp_left (spectralAbsApprox_zero n), ?_⟩
  exact (closure_mono (Function.support_comp_subset (spectralAbsApprox_zero n) f)).trans hf.2.2

/-- These approximants decrease the actual original Fourier energy. -/
theorem energy_spectralAbsApprox_le_of_core {f : ℝ → ℝ} (hf : IsCore f) (n : ℕ) :
    energy (fun x => spectralAbsApprox n (f x)) (fun x => spectralAbsApprox n (f x)) ≤ energy f f := by
  apply energy_comp_le_of_core hf.1 hf.2.1 (spectralAbsApprox_contDiff n) (spectralAbsApprox_zero n)
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    (spectralAbsApprox_lipschitz n).dist_le_mul x y

/-- For a fixed L² density, the actual smooth absolute-value
approximations converge to its absolute value in L². -/
theorem tendsto_eLpNorm_spectralAbsApprox {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun n => eLpNorm (fun x => spectralAbsApprox n (f x) - |f x|) 2 volume)
      atTop (𝓝 0) := by
  apply Torsion.tendsto_eLpNorm_two_of_dominated (B := fun x => 2 * ‖f x‖)
  · intro n
    exact ((spectralAbsApprox_contDiff n).continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable).sub
      (by simpa only [Real.norm_eq_abs] using hf.aestronglyMeasurable.norm)
  · have hsq : Integrable (fun x => ‖f x‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
    simpa only [mul_pow] using hsq.const_mul ((2 : ℝ) ^ 2)
  · intro n
    exact ae_of_all _ fun x => by
      have hbound := norm_sub_le (spectralAbsApprox n (f x)) |f x|
      have hnorm := spectralAbsApprox_norm_le n (f x)
      simpa only [Real.norm_eq_abs, abs_abs, two_mul] using
        hbound.trans (add_le_add hnorm (le_refl ‖|f x|‖))
  · exact ae_of_all _ fun x => by
      simpa only [sub_self] using (tendsto_spectralAbsApprox (f x)).sub_const |f x|

/-- Joint L² convergence permits the same approximation index to smooth
each member of an original core-approximating sequence. -/
theorem tendsto_eLpNorm_spectralAbsApprox_joint {f : ℝ → ℝ} {v : ℕ → ℝ → ℝ}
    (hf : MemLp f 2 volume) (hv : ∀ n, AEStronglyMeasurable (v n) volume)
    (hval : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => spectralAbsApprox n (v n x) - |f x|) 2 volume)
      atTop (𝓝 0) := by
  have hfirst : Tendsto (fun n => eLpNorm
      (fun x => spectralAbsApprox n (v n x) - spectralAbsApprox n (f x)) 2 volume) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hval (fun _ => bot_le)
    intro n
    apply eLpNorm_mono_ae
      (((spectralAbsApprox_contDiff n).continuous.comp_aestronglyMeasurable (hv n)).sub
        ((spectralAbsApprox_contDiff n).continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable))
    exact ae_of_all _ fun x => by
      simpa only [Pi.sub_apply, NNReal.coe_one, one_mul] using
        (spectralAbsApprox_lipschitz n).norm_sub_le (v n x) (f x)
  have hsecond := tendsto_eLpNorm_spectralAbsApprox hf
  have hsum := hfirst.add hsecond
  simp only [zero_add] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
  intro n
  have heq : (fun x => spectralAbsApprox n (v n x) - |f x|) =
      (fun x => spectralAbsApprox n (v n x) - spectralAbsApprox n (f x)) +
      (fun x => spectralAbsApprox n (f x) - |f x|) := by
    funext x
    simp only [Pi.add_apply]
    ring
  dsimp only
  rw [heq]
  exact eLpNorm_add_le (by norm_num)

/-- Every original form member has actual restricted-core approximations
to its absolute value, with asymptotically no larger Fourier energy. This
is the concrete sequence needed by closed-graph weak compactness. -/
theorem MemRestrictedFormDomain.exists_abs_core_approximation {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) :
    ∃ v w : ℕ → ℝ → ℝ,
      (∀ n, IsCore (v n)) ∧ (∀ n, IsCore (w n)) ∧
      Tendsto (fun n => eLpNorm (fun x => w n x - |f x|) 2 volume) atTop (𝓝 0) ∧
      (∀ n, energy (w n) (w n) ≤ energy (v n) (v n)) ∧
      Tendsto (fun n => energy (v n) (v n)) atTop (𝓝 (energy f f)) := by
  obtain ⟨v, hv, hval, henergy⟩ := hf.2.2.2
  refine ⟨v, fun n x => spectralAbsApprox n (v n x), hv,
    fun n => (hv n).spectralAbsApprox n, ?_,
    fun n => energy_spectralAbsApprox_le_of_core (hv n) n, ?_⟩
  · exact tendsto_eLpNorm_spectralAbsApprox_joint hf.1
      (fun n => (hv n).1.continuous.aestronglyMeasurable) hval
  · exact energy_tendsto_of_difference hf.integrable
      (fun n => (hv n).1.continuous.integrable_of_hasCompactSupport (hv n).2.1)
      hf.2.1 (fun n => finiteEnergy_of_contDiff_hasCompactSupport (hv n).1 (hv n).2.1) henergy

end Torsion.Spectral

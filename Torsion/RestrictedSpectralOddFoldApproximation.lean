module

public import Torsion.RestrictedSpectralOddFold

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual L² convergence of the flat odd-fold approximants

A common 1-Lipschitz scalar bound permits one diagonal approximation index
for the original core sequence and the shrinking flat value cutoff.
Spatial odd folding changes no pointwise norm of the approximation error.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

theorem tendsto_eLpNorm_oddFoldAbsApprox {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun n => eLpNorm (fun x => oddFoldAbsApprox n (f x) - |f x|) 2 volume)
      atTop (𝓝 0) := by
  apply Torsion.tendsto_eLpNorm_two_of_dominated (B := fun x => 2 * ‖f x‖)
  · intro n
    exact ((oddFoldAbsApprox_contDiff n).continuous.comp_aestronglyMeasurable hf.1).sub
      (by simpa only [Real.norm_eq_abs] using hf.1.norm)
  · have hsq : Integrable (fun x => ‖f x‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hf.1).1 hf
    simpa only [mul_pow] using hsq.const_mul ((2 : ℝ) ^ 2)
  · intro n
    exact ae_of_all _ fun x => by
      have hbound := norm_sub_le (oddFoldAbsApprox n (f x)) |f x|
      have hnorm := oddFoldAbsApprox_norm_le n (f x)
      simpa only [Real.norm_eq_abs, abs_abs, two_mul] using
        hbound.trans (add_le_add hnorm (le_refl ‖|f x|‖))
  · exact ae_of_all _ fun x => by
      simpa only [sub_self] using (tendsto_oddFoldAbsApprox (f x)).sub_const |f x|

/-- Joint scalar convergence of the shrinking flat approximation and an
actual varying L² approximation sequence. -/
theorem tendsto_eLpNorm_oddFoldAbsApprox_joint {f : ℝ → ℝ} {v : ℕ → ℝ → ℝ}
    (hf : MemLp f 2 volume) (hv : ∀ n, AEStronglyMeasurable (v n) volume)
    (hval : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => oddFoldAbsApprox n (v n x) - |f x|) 2 volume)
      atTop (𝓝 0) := by
  have hfirst : Tendsto (fun n => eLpNorm
      (fun x => oddFoldAbsApprox n (v n x) - oddFoldAbsApprox n (f x)) 2 volume) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hval (fun _ => zero_le _)
    intro n
    apply eLpNorm_mono_ae
    exact ae_of_all _ fun x => by
      simpa only [NNReal.coe_one, one_mul] using
        (oddFoldAbsApprox_lipschitz n).norm_sub_le (v n x) (f x)
  have hsecond := tendsto_eLpNorm_oddFoldAbsApprox hf
  have hsum := hfirst.add hsecond
  simp only [zero_add] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le _)
  intro n
  have heq : (fun x => oddFoldAbsApprox n (v n x) - |f x|) =
      (fun x => oddFoldAbsApprox n (v n x) - oddFoldAbsApprox n (f x)) +
      (fun x => oddFoldAbsApprox n (f x) - |f x|) := by
    funext x
    simp only [Pi.add_apply]
    ring
  dsimp only
  rw [heq]
  apply eLpNorm_add_le
  · exact ((oddFoldAbsApprox_contDiff n).continuous.comp_aestronglyMeasurable (hv n)).sub
      ((oddFoldAbsApprox_contDiff n).continuous.comp_aestronglyMeasurable hf.1)
  · exact ((oddFoldAbsApprox_contDiff n).continuous.comp_aestronglyMeasurable hf.1).sub
      (by simpa only [Real.norm_eq_abs] using hf.1.norm)
  · norm_num

/-- The spatial sign changes neither absolute-value nor L² convergence of
the actual approximation error. -/
theorem norm_oddFoldComp_sub_oddFoldAbs (Φ v f : ℝ → ℝ) (x : ℝ) :
    ‖oddFoldComp Φ v x - oddFoldAbs f x‖ = ‖Φ (v x) - |f x|‖ := by
  by_cases hx : 0 ≤ x
  · simp [oddFoldComp, oddFoldAbs, hx]
  · simp only [oddFoldComp, oddFoldAbs, if_neg hx]
    have heq : -Φ (v x) - -|f x| = -(Φ (v x) - |f x|) := by ring
    rw [heq, norm_neg]

/-- Concrete odd-folded smooth approximants converge to the actual folded
absolute value in the original global L² norm. -/
theorem tendsto_eLpNorm_oddFoldComp_joint {f : ℝ → ℝ} {v : ℕ → ℝ → ℝ}
    (hf : MemLp f 2 volume) (hv : ∀ n, AEStronglyMeasurable (v n) volume)
    (hval : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (fun x => oddFoldComp (oddFoldAbsApprox n) (v n) x - oddFoldAbs f x) 2 volume)
      atTop (𝓝 0) := by
  have heq (n : ℕ) :
      eLpNorm (fun x => oddFoldComp (oddFoldAbsApprox n) (v n) x - oddFoldAbs f x) 2 volume =
        eLpNorm (fun x => oddFoldAbsApprox n (v n x) - |f x|) 2 volume :=
    eLpNorm_congr_norm_ae (ae_of_all _ fun x => norm_oddFoldComp_sub_oddFoldAbs _ _ _ x)
  simpa only [heq] using tendsto_eLpNorm_oddFoldAbsApprox_joint hf hv hval

end Torsion.Spectral

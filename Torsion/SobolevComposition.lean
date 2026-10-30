import Torsion.SobolevGraph
import Torsion.Sobolev
import Torsion.L2Dominated
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Smooth Lipschitz chain rules in the actual zero-boundary Sobolev graph -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace Torsion

/-- The classical gradient chain rule for a real scalar outer function. -/
theorem gradient_comp_real {Ψ : ℝ → ℝ} {f : Plane → ℝ}
    (hΨ : Differentiable ℝ Ψ) (hf : Differentiable ℝ f) (x : Plane) :
    gradient (Ψ ∘ f) x = deriv Ψ (f x) • gradient f x := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have h := (hΨ (f x)).hasDerivAt.comp_hasFDerivAt x (hf x).hasGradientAt.hasFDerivAt
  simpa only [map_smul, RCLike.conj_to_real] using h

/-- Smooth scalar composition fixing zero preserves the actual test core. -/
theorem IsTest.comp_smooth {D : Set Plane} {f : Plane → ℝ} {Ψ : ℝ → ℝ}
    (hf : IsTest D f) (hΨ : ContDiff ℝ ∞ Ψ) (hzero : Ψ 0 = 0) :
    IsTest D (Ψ ∘ f) := by
  refine ⟨hΨ.comp hf.1, hf.2.1.comp_left hzero, ?_⟩
  exact (closure_mono (Function.support_comp_subset hzero f)).trans hf.2.2

/-- Lipschitz scalar composition preserves L² convergence of values. -/
theorem tendsto_eLpNorm_lipschitz_comp {Ψ : ℝ → ℝ} {C : ℝ≥0}
    (hLip : LipschitzWith C Ψ) {uₙ : ℕ → Plane → ℝ} {u : Plane → ℝ}
    (hval : Tendsto (fun n => eLpNorm (fun x => uₙ n x - u x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Ψ (uₙ n x) - Ψ (u x)) 2 volume)
      atTop (𝓝 0) := by
  have hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (C : ℝ)) hval
    (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le _)
  intro n
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (Eventually.of_forall (fun x => hLip.norm_sub_le (uₙ n x) (u x))) 2

/-- The genuine smooth Lipschitz chain rule in the original H¹₀ graph.
An a.e.-convergent subsequence of the supplied smooth approximations suffices;
bounded coefficient dominated convergence passes their classical gradients to
the claimed weak gradient. No Sobolev chain rule is assumed. -/
theorem MemH10.comp_smooth_lipschitz {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) {Ψ : ℝ → ℝ} {C : ℝ≥0}
    (hΨ : ContDiff ℝ ∞ Ψ) (hLip : LipschitzWith C Ψ) (hzero : Ψ 0 = 0) :
    MemH10 D (Ψ ∘ u) (fun x => deriv Ψ (u x) • g x) := by
  obtain ⟨hmu, hmg, f, hf, hval, hgrad⟩ := hu
  have hderiv : Continuous (deriv Ψ) := hΨ.continuous_deriv (by simp)
  have hameas : AEStronglyMeasurable (fun x => deriv Ψ (u x)) volume :=
    hderiv.comp_aestronglyMeasurable hmu.1
  have hbound : ∀ᵐ x ∂volume, ‖deriv Ψ (u x)‖ ≤ (C : ℝ) :=
    Eventually.of_forall (fun _ => norm_deriv_le_of_lipschitz hLip)
  have htarget : MemLp (fun x => deriv Ψ (u x) • g x) 2 volume :=
    memLp_bounded_coeff_smul hameas hmg hbound
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun n => (hf n).1.continuous.aestronglyMeasurable) hmu.1 hval
  obtain ⟨ν, hν, hνae⟩ := hmeasure.exists_seq_tendsto_ae
  have hvalsub := hval.comp hν.tendsto_atTop
  have hgradsub := hgrad.comp hν.tendsto_atTop
  have han (n : ℕ) : AEStronglyMeasurable (fun x => deriv Ψ (f (ν n) x)) volume :=
    (hderiv.comp (hf (ν n)).1.continuous).aestronglyMeasurable
  have hbn (n : ℕ) : ∀ᵐ x ∂volume, ‖deriv Ψ (f (ν n) x)‖ ≤ (C : ℝ) :=
    Eventually.of_forall (fun _ => norm_deriv_le_of_lipschitz hLip)
  have halim : ∀ᵐ x ∂volume, Tendsto (fun n => deriv Ψ (f (ν n) x)) atTop
      (𝓝 (deriv Ψ (u x))) := by
    filter_upwards [hνae] with x hx
    exact (hderiv.tendsto (u x)).comp hx
  have hprod := tendsto_eLpNorm_bounded_coeff_smul_joint han hameas
    (fun n => (hf (ν n)).memLp_gradient) hmg hbn hbound halim hgradsub
  refine ⟨hLip.comp_memLp hzero hmu, htarget,
    (fun n => Ψ ∘ f (ν n)), (fun n => (hf (ν n)).comp_smooth hΨ hzero),
    tendsto_eLpNorm_lipschitz_comp hLip hvalsub, ?_⟩
  have heq (n : ℕ) : gradient (Ψ ∘ f (ν n)) =
      fun x => deriv Ψ (f (ν n) x) • gradient (f (ν n)) x := by
    funext x
    exact gradient_comp_real (hΨ.differentiable (by simp))
      ((hf (ν n)).1.differentiable (by simp)) x
  simpa only [heq] using hprod

end Torsion

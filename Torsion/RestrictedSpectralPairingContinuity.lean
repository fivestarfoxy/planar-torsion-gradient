import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Support

/-! Continuity of actual integral pairings under L¹ convergence. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Torsion.Spectral

/-- Pairing with a continuous compactly supported test function preserves
actual L¹ convergence, directly through its global norm bound. -/
theorem integral_mul_tendsto_of_integral_norm_sub {u : ℝ → ℝ} {v : ℕ → ℝ → ℝ}
    (hu : Integrable u) (hv : ∀ n, Integrable (v n))
    (hlim : Tendsto (fun n => ∫ x : ℝ, ‖v n x - u x‖) atTop (𝓝 0))
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ x : ℝ, v n x * ψ x) atTop (𝓝 (∫ x : ℝ, u x * ψ x)) := by
  obtain ⟨C, hC⟩ := hcψ.exists_bound_of_continuous hψ
  have hprod {f : ℝ → ℝ} (hf : Integrable f) : Integrable (fun x => f x * ψ x) := by
    simpa only [mul_comm] using hf.bdd_mul hψ.aestronglyMeasurable ⟨C, hC⟩
  have hbound (n : ℕ) : ‖(∫ x : ℝ, v n x * ψ x) - ∫ x : ℝ, u x * ψ x‖ ≤
      C * (∫ x : ℝ, ‖v n x - u x‖) := by
    rw [← integral_sub (hprod (hv n)) (hprod hu)]
    have h := norm_integral_le_of_norm_le (((hv n).sub hu).norm.const_mul C)
      (ae_of_all _ fun x => show ‖v n x * ψ x - u x * ψ x‖ ≤ C * ‖v n x - u x‖ from by
        rw [← sub_mul, norm_mul]
        exact (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)).trans_eq (mul_comm _ _))
    simpa only [integral_const_mul] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) hbound (by simpa only [mul_zero] using hlim.const_mul C)

end Torsion.Spectral

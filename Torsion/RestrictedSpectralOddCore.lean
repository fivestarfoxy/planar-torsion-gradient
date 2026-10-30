module

public import Torsion.RestrictedSpectralEnergyContinuity
public import Torsion.RestrictedSpectralCorePrimitive

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual odd core approximation of an odd restricted form member

Antisymmetrizing the original defining core approximants preserves the
actual smooth restricted core. Reflection is an isometry for both the
actual L² seminorm and the actual Fourier energy, so both defining error
limits are preserved. No odd-core density assumption is introduced.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- Every pointwise odd member of the original restricted form has actual
pointwise odd core approximants, converging in its original value and
half-energy norms and in the actual diagonal energy. -/
theorem MemRestrictedFormDomain.exists_odd_core_approximation {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f) :
    ∃ w : ℕ → ℝ → ℝ,
      (∀ n, IsCore (w n) ∧ Function.Odd (w n)) ∧
      Tendsto (fun n => eLpNorm (fun x => w n x - f x) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => energy (fun x => w n x - f x) (fun x => w n x - f x)) atTop (𝓝 0) ∧
      Tendsto (fun n => energy (w n) (w n)) atTop (𝓝 (energy f f)) := by
  obtain ⟨v, hv, hL, hE⟩ := hf.2.2.2
  let w : ℕ → ℝ → ℝ := fun n x => (v n x - v n (-x)) / 2
  let e : ℕ → ℝ → ℝ := fun n x => v n x - f x
  have hvL (n : ℕ) : MemLp (v n) 2 volume :=
    (hv n).1.continuous.memLp_of_hasCompactSupport (hv n).2.1
  have heL (n : ℕ) : MemLp (e n) 2 volume := (hvL n).sub hf.1
  have heForm (n : ℕ) : MemRestrictedFormDomain (e n) := by
    simpa only [e, sub_eq_add_neg, neg_one_mul] using
      (hv n).memRestrictedFormDomain.add (hf.const_mul (-1))
  have hW (n : ℕ) : IsCore (w n) ∧ Function.Odd (w n) := by
    constructor
    · convert (hv n).linear_combination (hv n).reflect (1 / 2) (-1 / 2) using 1
      funext x
      dsimp only [w]
      ring
    · intro x
      dsimp only [w]
      rw [neg_neg]
      ring
  have herr (n : ℕ) : (fun x => w n x - f x) =
      (1 / 2 : ℝ) • (fun x => e n x + -(e n (-x))) := by
    funext x
    dsimp only [w, e, Pi.smul_apply, smul_eq_mul]
    rw [hodd x]
    ring
  have hnegNorm (n : ℕ) : eLpNorm (fun x => -(e n (-x))) 2 volume =
      eLpNorm (e n) 2 volume := by
    rw [show (fun x => -(e n (-x))) = -(e n ∘ (fun x : ℝ => -x)) by rfl, eLpNorm_neg]
    exact eLpNorm_comp_measurePreserving (heL n).aestronglyMeasurable (Measure.measurePreserving_neg volume)
  have hSumL : Tendsto (fun n => eLpNorm (fun x => e n x + -(e n (-x))) 2 volume)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [e, zero_add] using hL.add hL)
    · intro n
      exact bot_le
    · intro n
      dsimp only
      calc
        _ ≤ eLpNorm (e n) 2 volume + eLpNorm (fun x => -(e n (-x))) 2 volume :=
          eLpNorm_add_le (by norm_num)
        _ = _ := by rw [hnegNorm]
  have hWL : Tendsto (fun n => eLpNorm (fun x => w n x - f x) 2 volume) atTop (𝓝 0) := by
    simp_rw [herr, eLpNorm_const_smul]
    simpa using ENNReal.Tendsto.const_mul hSumL (Or.inr (enorm_ne_top (x := (1 / 2 : ℝ))))
  have hWE : Tendsto (fun n => energy (fun x => w n x - f x) (fun x => w n x - f x))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE
      (fun n => energy_nonneg _)
    intro n
    dsimp only
    have heI : Integrable (e n) := (heForm n).integrable
    have heF : FiniteEnergy (e n) := (heForm n).2.1
    have hnegF : FiniteEnergy (fun x => -(e n (-x))) := by
      simpa only [neg_one_mul] using
        FiniteEnergy.const_mul heI.comp_neg heF.reflect (-1)
    have hsum := energy_add_self_le heI heI.comp_neg.neg heF hnegF
    have hnegE : energy (fun x => -(e n (-x))) (fun x => -(e n (-x))) =
        energy (e n) (e n) := by
      have hfun : (fun x => -(e n (-x))) = fun x => (-1 : ℝ) * e n (-x) := by funext x; ring
      rw [hfun, energy_const_mul_self, energy_reflect]
      norm_num
    change energy (fun x => e n x + -(e n (-x))) (fun x => e n x + -(e n (-x))) ≤
      2 * energy (e n) (e n) + 2 * energy (fun x => -(e n (-x))) (fun x => -(e n (-x))) at hsum
    rw [hnegE] at hsum
    have herr' : (fun x => w n x - f x) =
        fun x => (1 / 2 : ℝ) * (e n x + -(e n (-x))) := herr n
    rw [herr', energy_const_mul_self]
    change (1 / 2 : ℝ) ^ 2 * energy (fun x => e n x + -(e n (-x)))
      (fun x => e n x + -(e n (-x))) ≤ energy (e n) (e n)
    nlinarith only [hsum]
  refine ⟨w, hW, hWL, hWE, ?_⟩
  exact energy_tendsto_of_difference hf.integrable
    (fun n => (hW n).1.memRestrictedFormDomain.integrable) hf.2.1
    (fun n => (hW n).1.memRestrictedFormDomain.2.1) hWE

end Torsion.Spectral

module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Positive local reparameterization at a regular boundary point

A positive nonzero scalar derivative gives an actual local inverse carrying
positive approaches to positive approaches. This is an ordinary calculus
result used to compare a boundary chart with a straight normal coordinate.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace Torsion

/-- A strictly differentiable scalar chart with positive derivative has an
actual local inverse that preserves approaches from the positive side. -/
theorem exists_positive_local_inverse {f : ℝ → ℝ} {c : ℝ}
    (hf : HasStrictDerivAt f c 0) (hf0 : f 0 = 0) (hc : 0 < c) :
    ∃ τ : ℝ → ℝ, τ 0 = 0 ∧ HasDerivAt τ c⁻¹ 0 ∧
      Tendsto τ (𝓝[>] 0) (𝓝[>] 0) ∧
      (∀ᶠ y in 𝓝 0, f (τ y) = y) := by
  let τ := hf.localInverse f c 0 hc.ne'
  have hτ0 : τ 0 = 0 := by
    have h := (hf.hasStrictFDerivAt_equiv hc.ne').localInverse_apply_image
    simpa only [hf0] using h
  have hτ : HasDerivAt τ c⁻¹ 0 := by
    simpa only [hf0] using (hf.to_localInverse hc.ne').hasDerivAt
  have hτlim : Tendsto τ (𝓝[>] 0) (𝓝 0) := by
    simpa only [hτ0] using hτ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hslope : Tendsto (fun t : ℝ => τ t / t) (𝓝[>] 0) (𝓝 c⁻¹) := by
    simpa only [zero_add, hτ0, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hτ.tendsto_slope_zero_right
  have hslope_pos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < τ t / t :=
    hslope.eventually (Ioi_mem_nhds (inv_pos.mpr hc))
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] 0, τ t ∈ Ioi 0 := by
    filter_upwards [self_mem_nhdsWithin, hslope_pos] with t ht hp
    have htpos : 0 < t := ht
    change 0 < τ t
    simpa only [zero_mul] using (lt_div_iff₀ htpos).mp hp
  have hright : ∀ᶠ y in 𝓝 0, f (τ y) = y := by
    simpa only [hf0] using (hf.hasStrictFDerivAt_equiv hc.ne').eventually_right_inverse
  exact ⟨τ, hτ0, hτ, tendsto_nhdsWithin_iff.mpr ⟨hτlim, hpositive⟩, hright⟩

end Torsion

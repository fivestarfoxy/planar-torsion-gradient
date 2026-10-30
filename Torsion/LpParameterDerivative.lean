module

public import Torsion.Definitions
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Group.Continuity

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Actual L² representatives of a parameter derivative -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion

/-- A derivative in the genuine L² Banach space gives convergence of the
pointwise weak-gradient difference quotients in the actual L² seminorm.
The a.e. representative algebra is proved, not assumed. -/
theorem lp_derivative_eLpNorm_quotient_tendsto
    {F : ℝ → Lp Plane 2 volume} {F' : Lp Plane 2 volume}
    (hF : HasDerivAt F F' 0) :
    Tendsto (fun t : ℝ => eLpNorm
      (fun z : Plane => t⁻¹ • ((F t : Plane → Plane) z - (F 0 : Plane → Plane) z) -
        (F' : Plane → Plane) z) 2 volume)
      (𝓝[≠] 0) (𝓝 0) := by
  have h := (hF.tendsto_slope_zero.sub_const F').enorm
  simp only [zero_add, sub_self, enorm_zero] at h
  convert h using 1
  funext t
  rw [Lp.enorm_def]
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (t⁻¹ • (F t - F 0)) F',
    Lp.coeFn_smul t⁻¹ (F t - F 0), Lp.coeFn_sub (F t) (F 0)] with z hsub hsmul hdiff
  simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul hdiff
  rw [hsub, hsmul, hdiff]

/-- The same derivative limit holds for any actual gradient representatives
identified with the L² classes, including identifications valid only near
the parameter origin. -/
theorem lp_derivative_eLpNorm_quotient_tendsto_of_ae_eq
    {F : ℝ → Lp Plane 2 volume} {F' : Lp Plane 2 volume}
    {g : ℝ → Plane → Plane} {h : Plane → Plane}
    (hF : HasDerivAt F F' 0)
    (hg : ∀ᶠ t : ℝ in 𝓝[≠] 0, g t =ᵐ[volume] (F t : Plane → Plane))
    (hg₀ : g 0 =ᵐ[volume] (F 0 : Plane → Plane))
    (hh : h =ᵐ[volume] (F' : Plane → Plane)) :
    Tendsto (fun t : ℝ =>
      eLpNorm (fun z : Plane => t⁻¹ • (g t z - g 0 z) - h z) 2 volume)
      (𝓝[≠] 0) (𝓝 0) := by
  apply (lp_derivative_eLpNorm_quotient_tendsto hF).congr'
  filter_upwards [hg] with t hgt
  apply eLpNorm_congr_ae
  filter_upwards [hgt, hg₀, hh] with z hz hz₀ hhz
  rw [hz, hz₀, hhz]

end Torsion

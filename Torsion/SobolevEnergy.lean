module

public import Torsion.SobolevPositivePart
public import Torsion.BoundedDomains
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Vanishing truncation energy forces actual Sobolev comparison

The positive-part test and its weak gradient have already been constructed
from the original graph approximation. Nonnegative energy forces this gradient
to vanish almost everywhere. The proved bounded-domain Poincaré inequality
then forces the positive-part value to vanish, giving the desired order.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- The positive-part energy pairing is exactly the squared norm of its
piecewise weak gradient. This identity also covers the zero level. -/
theorem positive_part_energy_identity (u : Plane → ℝ) (g : Plane → Plane) :
    (∫ x, inner (𝕜 := ℝ) (g x) (if 0 < u x then g x else 0)) =
      ∫ x, ‖if 0 < u x then g x else 0‖ ^ 2 := by
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hx : 0 < u x
  · simp only [if_pos hx, real_inner_self_eq_norm_sq]
  · simp only [if_neg hx, inner_zero_right, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]

/-- The actual positive-part energy is nonnegative. -/
theorem positive_part_energy_nonneg (u : Plane → ℝ) (g : Plane → Plane) :
    0 ≤ ∫ x, inner (𝕜 := ℝ) (g x) (if 0 < u x then g x else 0) := by
  rw [positive_part_energy_identity]
  exact integral_nonneg (fun x => sq_nonneg _)

/-- On a bounded domain, zero weak gradient forces the actual zero-boundary
Sobolev value to vanish, by the proved Poincaré estimate. -/
theorem MemH10.value_ae_zero_of_gradient_ae_zero {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : MemH10 D u g)
    (hbounded : Bornology.IsBounded D) (hgzero : g =ᵐ[volume] 0) :
    u =ᵐ[volume] 0 := by
  obtain ⟨K, hK, hp⟩ := exists_poincare_constant_of_bounded hbounded
  have hineq := hp u g hu
  rw [eLpNorm_eq_zero_of_ae_zero hgzero, mul_zero] at hineq
  have hz : eLpNorm u 2 volume = 0 := le_antisymm hineq zero_le
  exact (eLpNorm_eq_zero_iff (by norm_num)).mp hz

/-- Zero Dirichlet energy forces the actual L² weak gradient to vanish. -/
theorem MemH10.gradient_ae_zero_of_energy_eq_zero {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : MemH10 D u g)
    (henergy : (∫ x, ‖g x‖ ^ 2) = 0) : g =ᵐ[volume] 0 := by
  have hint : Integrable (fun x => ‖g x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hu.2.1.aestronglyMeasurable).mp hu.2.1
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖g x‖) hint).mp henergy
  filter_upwards [hz] with x hx
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- The genuine Sobolev truncation-energy argument for comparison: if testing
with the positive part gives zero energy, the value is nonpositive a.e. -/
theorem MemH10.nonpos_ae_of_pos_part_energy_eq_zero {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : MemH10 D u g)
    (hbounded : Bornology.IsBounded D)
    (henergy : (∫ x, inner (𝕜 := ℝ) (g x) (if 0 < u x then g x else 0)) = 0) :
    ∀ᵐ x ∂volume, u x ≤ 0 := by
  have hsq : (∫ x, ‖if 0 < u x then g x else 0‖ ^ 2) = 0 := by
    rw [← positive_part_energy_identity]
    exact henergy
  have hgradzero := hu.pos_part.gradient_ae_zero_of_energy_eq_zero hsq
  have hvalzero := hu.pos_part.value_ae_zero_of_gradient_ae_zero hbounded hgradzero
  filter_upwards [hvalzero] with x hx
  exact (le_max_left (u x) 0).trans (le_of_eq hx)

end Torsion

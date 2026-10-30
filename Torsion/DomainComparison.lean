module

public import Torsion.SobolevIdeal
public import Torsion.SobolevIntersection
public import Torsion.SobolevEnergy
public import Torsion.TorsionPositivity
public import Torsion.DirichletGalerkin

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual domain comparison for the weak torsion problem

The comparison test is constructed by the proved positive-part chain rule and
Sobolev ideal property. Testing the genuine weak equations gives zero energy,
and the proved Poincaré inequality gives the almost-everywhere order.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- The concrete real L² inner product agrees with the pointwise integral,
independently of the representatives chosen by `toLp`. -/
theorem inner_toLp_eq_integral_real_inner {g h : Plane → Plane}
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    inner (𝕜 := ℝ) (hg.toLp g) (hh.toLp h) =
      ∫ x, inner (𝕜 := ℝ) (g x) (h x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp, hh.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- Actual weak torsion solutions are monotone under inclusion of bounded
open domains. All order statements concern their zero-extended a.e. classes. -/
theorem IsWeakTorsion.mono {D E : Set Plane}
    {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hv : IsWeakTorsion E v h)
    (hD : IsOpen D) (hE : IsOpen E)
    (hbD : Bornology.IsBounded D) (hbE : Bornology.IsBounded E) (hDE : D ⊆ E) :
    ∀ᵐ x ∂volume, u x ≤ v x := by
  have hw : MemH10 E (fun x => u x - v x) (fun x => g x - h x) :=
    (hu.1.mono hDE).sub hv.1
  have hnonneg : ∀ᵐ x ∂volume, 0 ≤ Max.max (u x - v x) 0 :=
    Eventually.of_forall (fun x => le_max_right _ _)
  have hle : ∀ᵐ x ∂volume, Max.max (u x - v x) 0 ≤ u x := by
    filter_upwards [hu.nonneg_ae hbD, hv.nonneg_ae hbE] with x hx hy
    exact max_le (by linarith) hx
  have htest : MemH10 D (fun x => Max.max (u x - v x) 0)
      (fun x => if 0 < u x - v x then g x - h x else 0) :=
    hu.1.of_nonneg_le hw.pos_part hD hnonneg hle
  have horth := hu.galerkin_orthogonality hv hD.measurableSet hE.measurableSet hDE htest
  have hLp : hw.2.1.toLp (fun x => g x - h x) =
      hu.1.2.1.toLp g - hv.1.2.1.toLp h := hu.1.2.1.toLp_sub hv.1.2.1
  have henergy : (∫ x, inner (𝕜 := ℝ) (g x - h x)
      (if 0 < u x - v x then g x - h x else 0)) = 0 := by
    rw [← inner_toLp_eq_integral_real_inner hw.2.1 htest.2.1, hLp]
    exact horth
  have hnonpos := hw.nonpos_ae_of_pos_part_energy_eq_zero hbE henergy
  filter_upwards [hnonpos] with x hx
  exact sub_nonpos.mp hx

/-- Torsion is genuinely supermodular under union and intersection of
bounded open domains, as in Lemma 3.3. The positive defect is constructed in
the union Sobolev space and proved admissible in the actual intersection. -/
theorem IsWeakTorsion.supermodular {D₀ D₁ : Set Plane}
    {u₀ u₁ uU uJ : Plane → ℝ} {g₀ g₁ gU gJ : Plane → Plane}
    (hu₀ : IsWeakTorsion D₀ u₀ g₀) (hu₁ : IsWeakTorsion D₁ u₁ g₁)
    (huU : IsWeakTorsion (D₀ ∪ D₁) uU gU)
    (huJ : IsWeakTorsion (D₀ ∩ D₁) uJ gJ)
    (hD₀ : IsOpen D₀) (hD₁ : IsOpen D₁)
    (hb₀ : Bornology.IsBounded D₀) (hb₁ : Bornology.IsBounded D₁) :
    ∀ᵐ x ∂volume, u₀ x + u₁ x ≤ uU x + uJ x := by
  have hU : IsOpen (D₀ ∪ D₁) := hD₀.union hD₁
  have hJ : IsOpen (D₀ ∩ D₁) := hD₀.inter hD₁
  have hbU : Bornology.IsBounded (D₀ ∪ D₁) := hb₀.union hb₁
  have hbJ : Bornology.IsBounded (D₀ ∩ D₁) := hb₀.subset inter_subset_left
  have hJU : D₀ ∩ D₁ ⊆ D₀ ∪ D₁ := inter_subset_left.trans subset_union_left
  have hw : MemH10 (D₀ ∪ D₁)
      (fun x => u₀ x + u₁ x - uU x - uJ x)
      (fun x => g₀ x + g₁ x - gU x - gJ x) :=
    ((((hu₀.1.mono subset_union_left).add
      (hu₁.1.mono subset_union_right)).sub huU.1).sub (huJ.1.mono hJU))
  have htestU := hw.pos_part
  have hnonneg : ∀ᵐ x ∂volume,
      0 ≤ Max.max (u₀ x + u₁ x - uU x - uJ x) 0 :=
    Eventually.of_forall (fun x => le_max_right _ _)
  have hmono₀ := hu₀.mono huU hD₀ hU hb₀ hbU subset_union_left
  have hmono₁ := hu₁.mono huU hD₁ hU hb₁ hbU subset_union_right
  have hle₀ : ∀ᵐ x ∂volume, Max.max (u₀ x + u₁ x - uU x - uJ x) 0 ≤ u₀ x := by
    filter_upwards [hu₀.nonneg_ae hb₀, huJ.nonneg_ae hbJ, hmono₁] with x hx hj hm
    exact max_le (by linarith) hx
  have hle₁ : ∀ᵐ x ∂volume, Max.max (u₀ x + u₁ x - uU x - uJ x) 0 ≤ u₁ x := by
    filter_upwards [hu₁.nonneg_ae hb₁, huJ.nonneg_ae hbJ, hmono₀] with x hx hj hm
    exact max_le (by linarith) hx
  have htestJ : MemH10 (D₀ ∩ D₁)
      (fun x => Max.max (u₀ x + u₁ x - uU x - uJ x) 0)
      (fun x => if 0 < u₀ x + u₁ x - uU x - uJ x then
        g₀ x + g₁ x - gU x - gJ x else 0) :=
    hu₀.1.of_nonneg_le_inter hu₁.1 htestU hD₀ hD₁ hnonneg hle₀ hle₁
  have htest₀ := htestJ.mono inter_subset_left
  have htest₁ := htestJ.mono inter_subset_right
  have hweak₀ := hu₀.global_weak_equation hD₀.measurableSet htest₀
  have hweak₁ := hu₁.global_weak_equation hD₁.measurableSet htest₁
  have hweakU := huU.global_weak_equation hU.measurableSet htestU
  have hweakJ := huJ.global_weak_equation hJ.measurableSet htestJ
  have hLp : hw.2.1.toLp (fun x => g₀ x + g₁ x - gU x - gJ x) =
      hu₀.1.2.1.toLp g₀ + hu₁.1.2.1.toLp g₁ - huU.1.2.1.toLp gU - huJ.1.2.1.toLp gJ := by
    change (((hu₀.1.2.1.add hu₁.1.2.1).sub huU.1.2.1).sub huJ.1.2.1).toLp _ = _
    rw [MemLp.toLp_sub, MemLp.toLp_sub, MemLp.toLp_add]
  have henergy : (∫ x, inner (𝕜 := ℝ) (g₀ x + g₁ x - gU x - gJ x)
      (if 0 < u₀ x + u₁ x - uU x - uJ x then
        g₀ x + g₁ x - gU x - gJ x else 0)) = 0 := by
    rw [← inner_toLp_eq_integral_real_inner hw.2.1 htestJ.2.1, hLp,
      inner_sub_left, inner_sub_left, inner_add_left,
      hweak₀, hweak₁, hweakU, hweakJ]
    ring
  have hnonpos := hw.nonpos_ae_of_pos_part_energy_eq_zero hbU henergy
  filter_upwards [hnonpos] with x hx
  linarith

end Torsion

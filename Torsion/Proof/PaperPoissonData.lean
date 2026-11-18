module

public import Torsion.HilbertDirichlet
public import Torsion.DirichletGalerkin
public import Torsion.SobolevEnergy
public import Torsion.SobolevScalar

@[expose] public section

/-! # Solving and comparing zero-trace Poisson equations with square-integrable sources -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Torsion

/-- A zero-boundary Poisson solution with general source, tested on the entire Sobolev graph. -/
def IsL2Poisson (D : Set Plane) (f w : Plane → ℝ) (g : Plane → Plane) : Prop :=
  MemH10 D w g ∧ ∀ (v : Plane → ℝ) (h : Plane → Plane), MemH10 D v h →
    (∫ x, inner (𝕜 := ℝ) (g x) (h x)) = ∫ x, f x * v x

open HilbertDirichlet in
theorem exists_l2Poisson (D : ConvexDomain) {f : Plane → ℝ} (hf : MemLp f 2 volume) :
    ∃ w g, IsL2Poisson D.carrier f w g := by
  let ℓ : space D.carrier →L[ℝ] ℝ := (innerSL ℝ (hf.toLp f)).comp (valueMap D.carrier)
  let a := energy_coercive D
  let y := (InnerProductSpace.toDual ℝ (space D.carrier)).symm ℓ
  let p := a.continuousLinearEquivOfBilin.symm y
  have hp (q : space D.carrier) : energy D.carrier p q = ℓ q := by
    calc
      _ = inner (𝕜 := ℝ) (a.continuousLinearEquivOfBilin p) q :=
        (a.continuousLinearEquivOfBilin_apply p q).symm
      _ = inner (𝕜 := ℝ) y q := by rw [ContinuousLinearEquiv.apply_symm_apply]
      _ = ℓ q := InnerProductSpace.toDual_symm_apply
  refine ⟨valueMap D.carrier p, gradientMap D.carrier p, memH10_coordinates p, ?_⟩
  intro v h hv
  have hq := hp (ofMemH10 hv)
  change inner (𝕜 := ℝ) (gradientMap D.carrier p) (hv.2.1.toLp h) =
    inner (𝕜 := ℝ) (hf.toLp f) (hv.1.toLp v) at hq
  rw [L2.inner_def, L2.inner_def] at hq
  refine Eq.trans ?_ (hq.trans ?_)
  · apply integral_congr_ae
    filter_upwards [hv.2.1.coeFn_toLp] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hv.1.coeFn_toLp] with x hx hy
    simp [hx, hy, mul_comm]

theorem IsL2Poisson.const_smul {D : Set Plane} {f w : Plane → ℝ} {g : Plane → Plane}
    (hw : IsL2Poisson D f w g) (c : ℝ) :
    IsL2Poisson D (fun z => c * f z) (fun z => c • w z) (fun z => c • g z) := by
  refine ⟨hw.1.const_smul c, ?_⟩
  intro v h hv
  simp only [real_inner_smul_left, mul_assoc, integral_const_mul, hw.2 v h hv]

/-- Comparison allows source ordering just on the physical domain. -/
theorem IsL2Poisson.le_of_source_le {D : ConvexDomain} {f F u U : Plane → ℝ} {g G : Plane → Plane}
    (hu : IsL2Poisson D.carrier f u g) (hU : IsL2Poisson D.carrier F U G)
    (hf : MemLp f 2 volume) (hF : MemLp F 2 volume) (hle : ∀ z ∈ D.carrier, f z ≤ F z) :
    ∀ᵐ z ∂volume, u z ≤ U z := by
  let w (z : Plane) := u z - U z
  let k (z : Plane) := g z - G z
  have hw : MemH10 D.carrier w k := hu.1.sub hU.1
  let v (z : Plane) := max (w z) 0
  let h (z : Plane) := if 0 < w z then k z else 0
  have htest : MemH10 D.carrier v h := hw.pos_part
  have hnon : 0 ≤ ∫ z, inner (𝕜 := ℝ) (k z) (h z) := positive_part_energy_nonneg _ _
  have heq : (∫ z, inner (𝕜 := ℝ) (k z) (h z)) = 0 := by
    apply le_antisymm _ hnon
    simp only [k, inner_sub_left]
    rw [integral_sub (integrable_real_inner_of_memLp_two hu.1.2.1 htest.2.1)
      (integrable_real_inner_of_memLp_two hU.1.2.1 htest.2.1), hu.2 v h htest, hU.2 v h htest]
    apply sub_nonpos.mpr
    apply integral_mono_ae (hf.integrable_mul htest.1) (hF.integrable_mul htest.1)
    have ho := (ae_restrict_iff' D.isOpen.measurableSet.compl).mp htest.value_ae_zero_off
    filter_upwards [ho] with x hx
    by_cases hD : x ∈ D.carrier
    · exact mul_le_mul_of_nonneg_right (hle x hD) (le_max_right _ _)
    · have hv : v x = 0 := hx hD
      simp [hv]
  filter_upwards [hw.nonpos_ae_of_pos_part_energy_eq_zero D.bounded heq] with x hx
  exact sub_nonpos.mp hx

theorem IsWeakTorsion.l2Poisson_of_one_on {D : ConvexDomain} {u f : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D.carrier u g) (hone : ∀ z ∈ D.carrier, f z = 1) :
    IsL2Poisson D.carrier f u g := by
  refine ⟨hu.1, ?_⟩
  intro v h hv
  have hweak := hu.global_weak_equation D.isOpen.measurableSet hv
  rw [L2.inner_def] at hweak
  refine Eq.trans ?_ (hweak.trans ?_)
  · apply integral_congr_ae
    filter_upwards [hu.1.2.1.coeFn_toLp, hv.2.1.coeFn_toLp] with x hx hy
    rw [hx, hy]
  · apply integral_congr_ae
    have ho := (ae_restrict_iff' D.isOpen.measurableSet.compl).mp hv.value_ae_zero_off
    filter_upwards [ho] with x hx
    by_cases hz : x ∈ D.carrier
    · simp [hone _ hz]
    · have hzero : v x = 0 := hx hz
      simp [hzero]

end Torsion

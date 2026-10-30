import Torsion.ClassicalWeakTorsion
import Torsion.DomainComparison
import Torsion.WeakReflection.Poisson

/-!
# The actual torsion barrier of a containing slab

The nonnegative part of a compact cutoff of the exact slab polynomial is
an actual global Sobolev function. The original Sobolev ideal property
admits the positive comparison test on the original domain. Its weak
harmonic equation forces that test to vanish. No boundary regularity,
trace theorem or classical representative of the torsion solution is used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- The exact one-dimensional torsion polynomial of a horizontal slab. -/
def slabTorsionBarrier (a b : ℝ) (z : Plane) : ℝ :=
  (z.im - a) * (b - z.im) / 2

theorem slabTorsionBarrier_contDiff (a b : ℝ) :
    ContDiff ℝ ∞ (slabTorsionBarrier a b) :=
  ((Complex.imCLM.contDiff.sub contDiff_const).mul
    (contDiff_const.sub Complex.imCLM.contDiff)).div_const 2

theorem slabTorsionBarrier_hasGradientAt (a b : ℝ) (z : Plane) :
    HasGradientAt (slabTorsionBarrier a b) (((a + b) / 2 - z.im) • Complex.I) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hi := Complex.imCLM.hasFDerivAt (x := z)
  have h := ((hi.sub_const a).mul (hi.const_sub b)).mul_const (2⁻¹ : ℝ)
  convert h using 1
  ext v
  simp only [InnerProductSpace.toDual_apply, real_inner_smul_left]
  simp [Complex.inner, Complex.mul_re,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply]
  ring

theorem gradient_slabTorsionBarrier (a b : ℝ) (z : Plane) :
    gradient (slabTorsionBarrier a b) z =
      ((((a + b) / 2 - z.im : ℝ) : ℂ) * Complex.I) := by
  simpa only [Complex.real_smul] using (slabTorsionBarrier_hasGradientAt a b z).gradient

theorem slabTorsionBarrier_laplacian (a b : ℝ) (z : Plane) :
    WeakHarmonicRegularity.planarLaplacian (slabTorsionBarrier a b) z = -1 := by
  have hg : HasFDerivAt
      (fun w : Plane => ((((a + b) / 2 - w.im : ℝ) : ℂ) * Complex.I))
      _ z :=
    (Complex.ofRealCLM.hasFDerivAt.comp z
      ((hasFDerivAt_const ((a + b) / 2) z).sub Complex.imCLM.hasFDerivAt)).mul_const Complex.I
  unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
  rw [funext (gradient_slabTorsionBarrier a b)]
  rw [hg.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.mul_re, Complex.mul_im]

/-- Every actual weak torsion solution in a bounded open subset of a slab
is bounded above by the explicit slab torsion polynomial, almost everywhere
on the original domain. The domain need not be convex or boundary regular. -/
theorem IsWeakTorsion.le_slab_barrier {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g)
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) {a b : ℝ}
    (hslab : ∀ z ∈ D, a < z.im ∧ z.im < b) :
    ∀ᵐ z ∂volume.restrict D, u z ≤ slabTorsionBarrier a b z := by
  obtain ⟨η, hη, hηone⟩ := exists_test_eq_one_near_compact isOpen_univ
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hbD.closure) (subset_univ (closure D))
  let q := slabTorsionBarrier a b
  let p : Plane → ℝ := fun z => η z * q z
  have hp : IsTest univ p := hη.mul_left (slabTorsionBarrier_contDiff a b)
  have hpnear {z : Plane} (hz : z ∈ D) : p =ᶠ[𝓝 z] q := by
    have hone := hηone.filter_mono (nhds_le_nhdsSet (subset_closure hz))
    filter_upwards [hone] with w hw
    simp only [p, hw, one_mul]
  have hppos {z : Plane} (hz : z ∈ D) : 0 < p z := by
    rw [(hpnear hz).self_of_nhds]
    exact div_pos (mul_pos (sub_pos.mpr (hslab z hz).1)
      (sub_pos.mpr (hslab z hz).2)) (by norm_num)
  obtain ⟨R, _, hRB⟩ := (hbD.union hp.2.1.isCompact.isBounded).subset_ball_lt 0 (0 : Plane)
  let B := Metric.ball (0 : Plane) R
  have hDB : D ⊆ B := subset_union_left.trans hRB
  have hpB : IsTest B p := ⟨hp.1, hp.2.1, subset_union_right.trans hRB⟩
  let v : Plane → ℝ := fun z => max (p z) 0
  let h : Plane → Plane := fun z => if 0 < p z then gradient p z else 0
  have hv : MemH10 B v h := hpB.memH10.pos_part
  have huv : MemH10 B (fun z => u z - v z) (fun z => g z - h z) :=
    (hu.1.mono hDB).sub hv
  have htest : MemH10 D (fun z => max (u z - v z) 0)
      (fun z => if 0 < u z - v z then g z - h z else 0) := by
    apply hu.1.of_nonneg_le huv.pos_part hD
    · exact ae_of_all _ fun z => le_max_right _ _
    · filter_upwards [hu.nonneg_ae hbD] with z hz
      exact max_le (by dsimp only [v]; linarith [le_max_right (p z) 0]) hz
  have hgeq {z : Plane} (hz : z ∈ D) : h z = gradient q z := by
    simp only [h, if_pos (hppos hz)]
    unfold gradient
    rw [(hpnear hz).fderiv_eq]
  have hw : IsWeakHarmonicOn D (fun z => u z - v z) (fun z => g z - h z) := by
    refine ⟨huv.distributionalGradient, ?_⟩
    intro ψ hψ
    have hpde := classical_poisson_smooth_test_equation hD
      (slabTorsionBarrier_contDiff a b).contDiffOn
      (fun z _ => slabTorsionBarrier_laplacian a b z) hψ
    have heq : (∫ z, inner (𝕜 := ℝ) (h z) (gradient ψ z)) = ∫ z, ψ z := by
      rw [← hpde]
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change inner (𝕜 := ℝ) (h z) (gradient ψ z) =
          inner (𝕜 := ℝ) (gradient q z) (gradient ψ z)
        by_cases hz : z ∈ D
        · rw [hgeq hz]
        · rw [gradient_eq_zero_of_not_mem_tsupport (fun hs => hz (hψ.2.2 hs))]
          simp
    have hi := integrable_real_inner_of_memLp_two hu.1.2.1 (hψ.memLp_gradient (p := 2))
    have hj := integrable_real_inner_of_memLp_two hv.2.1 (hψ.memLp_gradient (p := 2))
    simp only [inner_sub_left]
    rw [integral_sub hi hj, hu.global_smooth_test_equation hψ, heq, sub_self]
  have henergy := hw.sobolev_test_equation huv.2.1 htest
  have horder := huv.nonpos_ae_of_pos_part_energy_eq_zero Metric.isBounded_ball henergy
  filter_upwards [ae_restrict_of_ae horder, ae_restrict_mem hD.measurableSet] with z hz hzD
  have hveq : v z = q z := by
    change max (p z) 0 = q z
    rw [max_eq_left (hppos hzD).le, (hpnear hzD).self_of_nhds]
  rw [hveq] at hz
  exact sub_nonpos.mp hz

/-- The slab polynomial lies below its tangent line at the lower boundary. -/
theorem slabTorsionBarrier_le_lower_linear (a b : ℝ) (z : Plane) :
    slabTorsionBarrier a b z ≤ (b - a) / 2 * (z.im - a) := by
  unfold slabTorsionBarrier
  nlinarith [sq_nonneg (z.im - a)]

/-- A crude uniform linear boundary barrier, with the exact slab width.
This is an actual a.e. estimate for the original weak solution. -/
theorem IsWeakTorsion.le_slab_lower_linear {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g)
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) {a b : ℝ}
    (hslab : ∀ z ∈ D, a < z.im ∧ z.im < b) :
    ∀ᵐ z ∂volume.restrict D, u z ≤ (b - a) / 2 * (z.im - a) := by
  filter_upwards [hu.le_slab_barrier hD hbD hslab] with z hz
  exact hz.trans (slabTorsionBarrier_le_lower_linear a b z)

/-- The same barrier holds pointwise for every continuous local
representative on an open subset of the original domain. This avoids
sampling an a.e. inequality on a special normal ray. -/
theorem IsWeakTorsion.le_slab_barrier_on_localRepresentative {D U : Set Plane}
    {u v : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g)
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) {a b : ℝ}
    (hslab : ∀ z ∈ D, a < z.im ∧ z.im < b)
    (hU : IsOpen U) (hUD : U ⊆ D) (hv : ContinuousOn v U)
    (hrep : u =ᵐ[volume.restrict U] v) :
    ∀ z ∈ U, v z ≤ slabTorsionBarrier a b z := by
  have hbound := ae_restrict_of_ae_restrict_of_subset hUD (hu.le_slab_barrier hD hbD hslab)
  have heq : (fun z => max (v z) (slabTorsionBarrier a b z)) =ᵐ[volume.restrict U]
      slabTorsionBarrier a b := by
    filter_upwards [hbound, hrep] with z hz he
    exact max_eq_right (he ▸ hz)
  have hq : ContinuousOn (slabTorsionBarrier a b) U :=
    (slabTorsionBarrier_contDiff a b).continuous.continuousOn
  have hpoint := Measure.eqOn_open_of_ae_eq heq hU (hv.sup hq) hq
  intro z hz
  exact max_eq_right_iff.mp (hpoint hz)

theorem IsWeakTorsion.le_slab_lower_linear_on_localRepresentative {D U : Set Plane}
    {u v : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g)
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) {a b : ℝ}
    (hslab : ∀ z ∈ D, a < z.im ∧ z.im < b)
    (hU : IsOpen U) (hUD : U ⊆ D) (hv : ContinuousOn v U)
    (hrep : u =ᵐ[volume.restrict U] v) :
    ∀ z ∈ U, v z ≤ (b - a) / 2 * (z.im - a) := by
  intro z hz
  exact (hu.le_slab_barrier_on_localRepresentative hD hbD hslab hU hUD hv hrep z hz).trans
    (slabTorsionBarrier_le_lower_linear a b z)

end Torsion

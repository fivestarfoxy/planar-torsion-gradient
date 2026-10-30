module

public import Torsion.WeakHarmonicRegularity
public import Torsion.SobolevCutoff
public import Torsion.SobolevLocalization

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Interior energy estimates for concrete weak harmonic functions

The smooth-test equation extends to the actual H¹₀ graph, and testing with
η²u yields Caccioppoli's estimate. These are interior regularity steps toward
Weyl's lemma; this module does not assert a fixed smooth representative.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

private theorem inner_toLp_eq_integral {g h : Plane → Plane}
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    inner (𝕜 := ℝ) (hg.toLp g) (hh.toLp h) = ∫ x, inner (𝕜 := ℝ) (g x) (h x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp, hh.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- The actual weak harmonic equation extends from smooth compact tests to
all zero-boundary Sobolev tests by continuity on the closed L² graph. -/
theorem IsWeakHarmonicOn.sobolev_test_equation {U : Set Plane}
    {u v : Plane → ℝ} {g h : Plane → Plane} (hw : IsWeakHarmonicOn U u g)
    (hg : MemLp g 2 volume) (hv : MemH10 U v h) :
    (∫ x, inner (𝕜 := ℝ) (g x) (h x)) = 0 := by
  let L : SobolevPair →L[ℝ] ℝ :=
    (innerSL ℝ (hg.toLp g)).comp (ContinuousLinearMap.snd ℝ _ _)
  have hker : H10Graph U ≤ LinearMap.ker L := by
    apply (testGraphSubmodule U).topologicalClosure_minimal
    · rintro p ⟨f, hf, rfl⟩
      change inner (𝕜 := ℝ) (hg.toLp g) (hf.memLp_gradient.toLp (gradient f)) = 0
      rw [inner_toLp_eq_integral]
      exact hw.2 f hf
    · exact ContinuousLinearMap.isClosed_ker L
  have heq := hker ((memH10_iff_mem_H10Graph hv.1 hv.2.1).mp hv)
  change inner (𝕜 := ℝ) (hg.toLp g) (hv.2.1.toLp h) = 0 at heq
  rwa [inner_toLp_eq_integral] at heq

private theorem norm_toLp_sq_eq_integral {g : Plane → Plane} (hg : MemLp g 2 volume) :
    ‖hg.toLp g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_eq_integral]
  simp only [real_inner_self_eq_norm_sq]

/-- Caccioppoli's local energy estimate in the actual L² norm. The value can
belong to H¹₀ on a different domain; only the cutoff lies inside the harmonic
region. No boundary smoothness, pointwise representative, or derivative
estimate is assumed. -/
theorem IsWeakHarmonicOn.caccioppoli_norm {U E : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hw : IsWeakHarmonicOn U u g)
    (hu : MemH10 E u g) {η : Plane → ℝ} (hη : IsTest U η) :
    ‖((hu.2.1.smul (hη.memLp_value (p := ∞))) :
      MemLp (fun x => η x • g x) 2 volume).toLp (fun x => η x • g x)‖ ≤
    2 * ‖((hη.memLp_gradient (p := ∞)).smul hu.1 :
      MemLp (fun x => u x • gradient η x) 2 volume).toLp
        (fun x => u x • gradient η x)‖ := by
  let A : Plane → Plane := fun x => η x • g x
  let B : Plane → Plane := fun x => u x • gradient η x
  have hA : MemLp A 2 volume := hu.2.1.smul (hη.memLp_value (p := ∞))
  have hB : MemLp B 2 volume := (hη.memLp_gradient (p := ∞)).smul hu.1
  have htest := (hu.mul_test hη).mul_test hη
  have hzero := hw.sobolev_test_equation hu.2.1 htest
  have hAA : Integrable (fun x => inner (𝕜 := ℝ) (A x) (A x)) volume :=
    integrable_real_inner_of_memLp_two hA hA
  have hAB : Integrable (fun x => inner (𝕜 := ℝ) (A x) (B x)) volume :=
    integrable_real_inner_of_memLp_two hA hB
  have hpoint (x : Plane) :
      inner (𝕜 := ℝ) (g x)
        (η x • (η x • g x + u x • gradient η x) +
          (η x * u x) • gradient η x) =
      inner (𝕜 := ℝ) (A x) (A x) + 2 * inner (𝕜 := ℝ) (A x) (B x) := by
    simp [A, B, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    ring
  simp only [hpoint] at hzero
  rw [integral_add hAA (hAB.const_mul 2), integral_const_mul,
    ← inner_toLp_eq_integral hA hA, ← inner_toLp_eq_integral hA hB,
    real_inner_self_eq_norm_sq] at hzero
  change ‖hA.toLp A‖ ≤ 2 * ‖hB.toLp B‖
  have hbound : -inner (𝕜 := ℝ) (hA.toLp A) (hB.toLp B) ≤
      ‖hA.toLp A‖ * ‖hB.toLp B‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  by_contra hn
  have hgt : 2 * ‖hB.toLp B‖ < ‖hA.toLp A‖ := lt_of_not_ge hn
  have hpos : 0 < ‖hA.toLp A‖ := by linarith [norm_nonneg (hB.toLp B)]
  have hp := mul_pos hpos (sub_pos.mpr hgt)
  nlinarith

/-- The integral form of the Caccioppoli estimate, including the
universal cutoff coefficient 4 from the standard quadratic test. -/
theorem IsWeakHarmonicOn.caccioppoli_energy {U E : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hw : IsWeakHarmonicOn U u g)
    (hu : MemH10 E u g) {η : Plane → ℝ} (hη : IsTest U η) :
    (∫ x, ‖η x • g x‖ ^ 2) ≤ 4 * ∫ x, ‖u x • gradient η x‖ ^ 2 := by
  have hA : MemLp (fun x => η x • g x) 2 volume :=
    hu.2.1.smul (hη.memLp_value (p := ∞))
  have hB : MemLp (fun x => u x • gradient η x) 2 volume :=
    (hη.memLp_gradient (p := ∞)).smul hu.1
  have hn := hw.caccioppoli_norm hu hη
  rw [← norm_toLp_sq_eq_integral hA, ← norm_toLp_sq_eq_integral hB]
  nlinarith [norm_nonneg (hA.toLp (fun x => η x • g x)),
    norm_nonneg (hB.toLp (fun x => u x • gradient η x))]

/-- A bounded cutoff gradient gives an energy estimate solely in terms of the
value's L² size. The scalar bound is an ordinary pointwise cutoff estimate. -/
theorem IsWeakHarmonicOn.caccioppoli_energy_of_gradient_bound {U E : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hw : IsWeakHarmonicOn U u g)
    (hu : MemH10 E u g) {η : Plane → ℝ} (hη : IsTest U η)
    {L : ℝ} (_hL : 0 ≤ L) (hbound : ∀ x, ‖gradient η x‖ ≤ L) :
    (∫ x, ‖η x • g x‖ ^ 2) ≤ 4 * L ^ 2 * ∫ x, (u x) ^ 2 := by
  have hB : MemLp (fun x => u x • gradient η x) 2 volume :=
    (hη.memLp_gradient (p := ∞)).smul hu.1
  have hintB := (memLp_two_iff_integrable_sq_norm hB.1).mp hB
  have hintU := hu.1.integrable_sq.mul_const (L ^ 2)
  have hineq : (∫ x, ‖u x • gradient η x‖ ^ 2) ≤
      ∫ x, (u x) ^ 2 * L ^ 2 := by
    apply integral_mono hintB hintU
    intro x
    dsimp only
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2) (sq_nonneg _)
  rw [integral_mul_const] at hineq
  have hbase := hw.caccioppoli_energy hu hη
  nlinarith

/-- On any measurable set where the cutoff is one, the full weak gradient has
the corresponding local Caccioppoli bound. -/
theorem IsWeakHarmonicOn.local_energy_le {U E K : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane} (hw : IsWeakHarmonicOn U u g)
    (hu : MemH10 E u g) {η : Plane → ℝ} (hη : IsTest U η)
    (hK : MeasurableSet K) (hηK : ∀ x ∈ K, η x = 1)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ x, ‖gradient η x‖ ≤ L) :
    (∫ x in K, ‖g x‖ ^ 2) ≤ 4 * L ^ 2 * ∫ x, (u x) ^ 2 := by
  have hA : MemLp (fun x => η x • g x) 2 volume :=
    hu.2.1.smul (hη.memLp_value (p := ∞))
  calc
    (∫ x in K, ‖g x‖ ^ 2) = ∫ x in K, ‖η x • g x‖ ^ 2 := by
      apply setIntegral_congr_fun hK
      intro x hx
      dsimp only
      rw [hηK x hx, one_smul]
    _ ≤ ∫ x, ‖η x • g x‖ ^ 2 :=
      setIntegral_le_integral ((memLp_two_iff_integrable_sq_norm hA.1).mp hA)
        (ae_of_all _ fun x => sq_nonneg _)
    _ ≤ _ := hw.caccioppoli_energy_of_gradient_bound hu hη hL hbound

/-- Every compact subset of an open harmonic region has a geometric interior
energy constant. The constant is constructed from a genuine smooth cutoff,
not supplied as an analytic estimate. -/
theorem exists_local_harmonic_energy_constant {U K : Set Plane}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ {E : Set Plane} {u : Plane → ℝ} {g : Plane → Plane},
      MemH10 E u g → IsWeakHarmonicOn U u g →
      (∫ x in K, ‖g x‖ ^ 2) ≤ C * ∫ x, (u x) ^ 2 := by
  obtain ⟨η, hη, hone⟩ := exists_test_eq_one_near_compact hU hK hKU
  obtain ⟨L, hL⟩ := (hasCompactSupport_gradient hη.2.1).exists_bound_of_continuous
    hη.continuous_gradient
  have hL0 : 0 ≤ L := (norm_nonneg (gradient η 0)).trans (hL 0)
  refine ⟨4 * L ^ 2 + 1, by positivity, ?_⟩
  intro E u g hu hw
  have hηK : ∀ x ∈ K, η x = 1 := fun x hx =>
    (hone.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds
  have hbase := hw.local_energy_le hu hη hK.measurableSet hηK hL0 hL
  have hnonneg : 0 ≤ ∫ x, (u x) ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  nlinarith

/-- Local strong gradient convergence follows from strong value convergence
for weakly harmonic pairs. This is an actual interior estimate, even though
constructing a smooth representative still requires the rest of Weyl's lemma. -/
theorem weak_harmonic_local_gradient_energy_tendsto {U K : Set Plane}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {E : ℕ → Set Plane} {u : ℕ → Plane → ℝ} {g : ℕ → Plane → Plane}
    (hmem : ∀ n, MemH10 (E n) (u n) (g n))
    (hweak : ∀ n, IsWeakHarmonicOn U (u n) (g n))
    (hval : Tendsto (fun n => ∫ x, (u n x) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in K, ‖g n x‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_local_harmonic_energy_constant hU hK hKU
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hval.const_mul C)
  · intro n
    exact integral_nonneg (fun x => sq_nonneg _)
  · intro n
    exact hbound (hmem n) (hweak n)

end Torsion

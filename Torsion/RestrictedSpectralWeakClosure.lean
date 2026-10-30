module

public import Torsion.RestrictedSpectralGraphHilbert
public import Torsion.CompactSpectral.WeakHilbertCompact

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Weak closure and lower semicontinuity of the actual restricted form

Uniformly bounded actual Fourier energy and strong L² convergence imply
membership in the original restricted form domain. Weak compactness is used
only in the already constructed complete Hilbert graph. Scalar continuous
linear functionals identify its value limit and give the half-derivative
norm bound, so no weak convergence or closure property is postulated.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform

namespace Torsion.Spectral

private theorem real_cluster_le {u : ℕ → ℝ} {x c : ℝ}
    (hx : MapClusterPt x atTop u) (hb : ∀ᶠ n in atTop, u n ≤ c) : x ≤ c := by
  have hle : Filter.map u atTop ≤ 𝓟 (Iic c) := le_principal_iff.mpr hb
  have hm : x ∈ closure (Iic c) := (hx.clusterPt.mono hle).mem_closure
  simpa only [isClosed_Iic.closure_eq, mem_Iic] using hm

private theorem real_cluster_eq_of_tendsto {u : ℕ → ℝ} {x y : ℝ}
    (ht : Tendsto u atTop (𝓝 y)) (hx : MapClusterPt x atTop u) : x = y := by
  let l : Filter ℝ := 𝓝 x ⊓ Filter.map u atTop
  haveI : NeBot l := hx.clusterPt.neBot
  have h₁ : Tendsto id l (𝓝 x) := by
    simpa only [Tendsto, Filter.map_id, l] using
      (inf_le_left : 𝓝 x ⊓ Filter.map u atTop ≤ 𝓝 x)
  have h₂ : Tendsto id l (𝓝 y) := by
    simpa only [Tendsto, Filter.map_id, l] using
      (le_trans (inf_le_right : 𝓝 x ⊓ Filter.map u atTop ≤ Filter.map u atTop) ht)
  exact tendsto_nhds_unique h₁ h₂

private theorem weak_eval_cluster {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℕ → E} {p : WeakSpace ℝ E}
    (hp : MapClusterPt p atTop (fun n => toWeakSpace ℝ E (u n)))
    (l : E →L[ℝ] ℝ) :
    MapClusterPt (l (p : E)) atTop (fun n => l (u n)) := by
  have hc : Continuous (fun z : WeakSpace ℝ E => l (z : E)) :=
    WeakBilin.eval_continuous (B := (topDualPairing ℝ E).flip) (y := l)
  simpa only [Function.comp_def] using!
    MapClusterPt.continuousAt_comp hc.continuousAt hp

/-- Weak graph cluster points preserve every eventual bound on the norm of
a bounded linear image. The proof tests against that image at the limit. -/
private theorem weak_map_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u : ℕ → E} {p : WeakSpace ℝ E}
    (hp : MapClusterPt p atTop (fun n => toWeakSpace ℝ E (u n)))
    (T : E →L[ℝ] F) {r : ℝ} (hr : 0 ≤ r)
    (hb : ∀ᶠ n in atTop, ‖T (u n)‖ ≤ r) : ‖T (p : E)‖ ≤ r := by
  let z : F := T (p : E)
  let l : E →L[ℝ] ℝ := (innerSL ℝ z).comp T
  have hcl := weak_eval_cluster hp l
  have hbound : ∀ᶠ n in atTop, l (u n) ≤ ‖z‖ * r := by
    filter_upwards [hb] with n hn
    exact (real_inner_le_norm z (T (u n))).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg z))
  have hs := real_cluster_le hcl hbound
  change inner (𝕜 := ℝ) z z ≤ ‖z‖ * r at hs
  rw [real_inner_self_eq_norm_sq, pow_two] at hs
  by_cases hz : ‖z‖ = 0
  · simpa only [z, hz] using hr
  · exact (mul_le_mul_iff_of_pos_left (lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz))).mp hs

/-- Actual form-domain membership and its actual Fourier energy are closed
under strong L² limits of sequences with eventually bounded energy. -/
theorem memRestrictedFormDomain_of_bounded_energy
    {f : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {B : ℝ}
    (hf : MemLp f 2 volume) (hv : ∀ n, MemRestrictedFormDomain (v n))
    (hL : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0))
    (hB : ∀ᶠ n in atTop, energy (v n) (v n) ≤ B) :
    MemRestrictedFormDomain f ∧ energy f f ≤ B := by
  let P : ℕ → RestrictedHilbert.space := fun n =>
    RestrictedHilbert.ofMemRestrictedFormDomain (hv n)
  have hB0 : 0 ≤ B := by
    obtain ⟨n, hn⟩ := hB.exists
    exact (energy_nonneg (v n)).trans hn
  have hA0 : 0 ≤ (8 / Real.pi + 2 * Real.pi) * B := by positivity
  have hhalfSq (n : ℕ) : ‖RestrictedHilbert.halfMap (P n)‖ ^ 2 =
      (2 * Real.pi) * energy (v n) (v n) := by
    rw [RestrictedHilbert.halfMap_ofMemRestrictedFormDomain,
      energy_self_eq_norm_halfDerivative (hv n).integrable (hv n).2.1]
    field_simp
  have hvalueSq (n : ℕ) : ‖RestrictedHilbert.valueMap (P n)‖ ^ 2 ≤
      (8 / Real.pi) * energy (v n) (v n) := by
    rw [RestrictedHilbert.valueMap_ofMemRestrictedFormDomain,
      ← integral_sq_eq_norm_toLp_sq (hv n).1]
    exact (hv n).fractional_poincare
  have hnorm : ∀ᶠ n in atTop, toWeakSpace ℝ RestrictedHilbert.space (P n) ∈
      Torsion.CompactSpectral.weakClosedBall
        (Real.sqrt ((8 / Real.pi + 2 * Real.pi) * B)) := by
    filter_upwards [hB] with n hn
    change P n ∈ Metric.closedBall (0 : RestrictedHilbert.space) _
    apply mem_closedBall_zero_iff.mpr
    have hs : ‖P n‖ ^ 2 ≤ (8 / Real.pi + 2 * Real.pi) * B := by
      rw [RestrictedHilbert.norm_sq, hhalfSq]
      have h₁ := hvalueSq n
      have h₂ := mul_le_mul_of_nonneg_left hn (show 0 ≤ (8 / Real.pi : ℝ) by positivity)
      have h₃ := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2 * Real.pi by positivity)
      nlinarith
    nlinarith [Real.sq_sqrt hA0, Real.sqrt_nonneg ((8 / Real.pi + 2 * Real.pi) * B),
      norm_nonneg (P n)]
  obtain ⟨p, _, hp⟩ := (Torsion.CompactSpectral.isCompact_weakClosedBall
    (𝕜 := ℝ) (E := RestrictedHilbert.space)
    (Real.sqrt ((8 / Real.pi + 2 * Real.pi) * B))).exists_mapClusterPt_of_frequently hnorm.frequently
  have hvalue : RestrictedHilbert.valueMap (p : RestrictedHilbert.space) = hf.toLp f := by
    have hval : Tendsto (fun n => RestrictedHilbert.valueMap (P n)) atTop (𝓝 (hf.toLp f)) := by
      apply tendsto_iff_edist_tendsto_0.mpr
      simpa only [P, RestrictedHilbert.valueMap_ofMemRestrictedFormDomain,
        Lp.edist_toLp_toLp, Pi.sub_def] using hL
    let z : RestrictedHilbert.ValueL2 :=
      RestrictedHilbert.valueMap (p : RestrictedHilbert.space) - hf.toLp f
    let l : RestrictedHilbert.space →L[ℝ] ℝ :=
      (innerSL ℝ z).comp RestrictedHilbert.valueMap
    have hcl := weak_eval_cluster hp l
    have hlim : Tendsto (fun n => l (P n)) atTop (𝓝 (inner (𝕜 := ℝ) z (hf.toLp f))) :=
      ((innerSL ℝ z).continuous.tendsto _).comp hval
    have heq := real_cluster_eq_of_tendsto hlim hcl
    have hz : ‖z‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      change inner (𝕜 := ℝ) z
        (RestrictedHilbert.valueMap (p : RestrictedHilbert.space) - hf.toLp f) = 0
      rw [inner_sub_right]
      change inner (𝕜 := ℝ) z (RestrictedHilbert.valueMap (p : RestrictedHilbert.space)) =
        inner (𝕜 := ℝ) z (hf.toLp f) at heq
      rw [heq, sub_self]
    exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hz))
  have hrep : (RestrictedHilbert.valueMap (p : RestrictedHilbert.space) : ℝ → ℝ) =ᵐ[volume] f := by
    rw [hvalue]
    exact hf.coeFn_toLp
  have hmem := (RestrictedHilbert.memRestrictedFormDomain_coordinates
    (p : RestrictedHilbert.space)).congr_ae hrep
  refine ⟨hmem, ?_⟩
  have hhalfBound : ∀ᶠ n in atTop, ‖RestrictedHilbert.halfMap (P n)‖ ≤
      Real.sqrt ((2 * Real.pi) * B) := by
    filter_upwards [hB] with n hn
    have hs := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2 * Real.pi by positivity)
    rw [← hhalfSq] at hs
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 * Real.pi) * B by positivity),
      Real.sqrt_nonneg ((2 * Real.pi) * B), norm_nonneg (RestrictedHilbert.halfMap (P n))]
  have hhalf := weak_map_norm_le hp RestrictedHilbert.halfMap
    (Real.sqrt_nonneg ((2 * Real.pi) * B)) hhalfBound
  have hhalfSqBound : ‖RestrictedHilbert.halfMap (p : RestrictedHilbert.space)‖ ^ 2 ≤
      (2 * Real.pi) * B := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 * Real.pi) * B by positivity),
      norm_nonneg (RestrictedHilbert.halfMap (p : RestrictedHilbert.space))]
  calc
    energy f f = energy
        (RestrictedHilbert.valueMap (p : RestrictedHilbert.space) : ℝ → ℝ)
        (RestrictedHilbert.valueMap (p : RestrictedHilbert.space) : ℝ → ℝ) :=
      (energy_congr_ae hrep hrep).symm
    _ = (1 / (2 * Real.pi)) * ‖RestrictedHilbert.halfMap (p : RestrictedHilbert.space)‖ ^ 2 := by
      rw [← RestrictedHilbert.energy_eq_original, RestrictedHilbert.energy_apply,
        real_inner_self_eq_norm_sq]
    _ ≤ (1 / (2 * Real.pi)) * ((2 * Real.pi) * B) :=
      mul_le_mul_of_nonneg_left hhalfSqBound (by positivity)
    _ = B := by field_simp

/-- Core-sequence version of actual weak closure and lower semicontinuity. -/
theorem memRestrictedFormDomain_of_core_bounded_energy
    {f : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {B : ℝ}
    (hf : MemLp f 2 volume) (hv : ∀ n, IsCore (v n))
    (hL : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0))
    (hB : ∀ᶠ n in atTop, energy (v n) (v n) ≤ B) :
    MemRestrictedFormDomain f ∧ energy f f ≤ B :=
  memRestrictedFormDomain_of_bounded_energy hf (fun n => (hv n).memRestrictedFormDomain) hL hB

/-- A convergent sequence of upper bounds is sufficient; energy convergence
of the approximating functions themselves is not assumed. -/
theorem memRestrictedFormDomain_of_core_energy_upper_tendsto
    {f : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {b : ℕ → ℝ} {B : ℝ}
    (hf : MemLp f 2 volume) (hv : ∀ n, IsCore (v n))
    (hL : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0))
    (hupper : ∀ᶠ n in atTop, energy (v n) (v n) ≤ b n)
    (hb : Tendsto b atTop (𝓝 B)) :
    MemRestrictedFormDomain f ∧ energy f f ≤ B := by
  have heps (ε : ℝ) (hε : 0 < ε) :
      MemRestrictedFormDomain f ∧ energy f f ≤ B + ε := by
    apply memRestrictedFormDomain_of_core_bounded_energy hf hv hL
    filter_upwards [hupper, hb.eventually (Iio_mem_nhds (by linarith : B < B + ε))]
      with n hn hbnd
    exact hn.trans hbnd.le
  refine ⟨(heps 1 (by norm_num)).1, ?_⟩
  exact le_of_forall_pos_le_add fun ε hε => (heps ε hε).2

end Torsion.Spectral

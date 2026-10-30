module

public import Torsion.SobolevBoundaryAdmission
public import Torsion.ClassicalWeakLaplacian
public import Torsion.SobolevEnergy
public import Torsion.TorsionTranslation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Positive-part maximum principle and translation comparison

A continuous function that is nonpositive off a bounded open set and harmonic
against its actual compact tests is nonpositive everywhere. Flat scalar
truncations are genuine compact tests; their nonnegative energy vanishes.
This does not require a global Sobolev gradient for the function itself.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace Torsion

/-- Nonpositive exterior values suffice for the compact flat truncation test.
No smoothness across the boundary is assumed. -/
theorem BoundaryAdmission.truncation_isTest_of_nonpos {D : Set Plane}
    (hD : IsOpen D) (hb : Bornology.IsBounded D) {u : Plane → ℝ}
    (hc : Continuous u) (hs : ContDiffOn ℝ ∞ u D)
    (hout : ∀ x ∉ D, u x ≤ 0) (n : ℕ) :
    IsTest D (fun x => BoundaryAdmission.truncation n (u x)) := by
  have hlevel : IsClosed {x : Plane | BoundaryAdmission.threshold n ≤ u x} :=
    isClosed_le continuous_const hc
  have hsupport : Function.support (fun x => BoundaryAdmission.truncation n (u x)) ⊆
      {x : Plane | BoundaryAdmission.threshold n ≤ u x} := by
    intro x hx
    by_contra h
    exact hx (BoundaryAdmission.truncation_zero_of_le n (le_of_not_ge h))
  have hts : tsupport (fun x => BoundaryAdmission.truncation n (u x)) ⊆
      {x : Plane | BoundaryAdmission.threshold n ≤ u x} := closure_minimal hsupport hlevel
  have htsD : tsupport (fun x => BoundaryAdmission.truncation n (u x)) ⊆ D := by
    intro x hx
    by_contra hxD
    exact (not_le_of_gt (BoundaryAdmission.threshold_pos n))
      ((hts hx).trans (hout x hxD))
  refine ⟨?_, Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
    (hb.subset htsD), htsD⟩
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ D
  · exact (BoundaryAdmission.truncation_contDiff n).contDiffAt.comp x
      ((hs x hx).contDiffAt (hD.mem_nhds hx))
  · have hevent : ∀ᶠ y in 𝓝 x, u y < BoundaryAdmission.threshold n :=
      hc.continuousAt.eventually_lt continuous_const.continuousAt
        ((hout x hx).trans_lt (BoundaryAdmission.threshold_pos n))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hevent] with y hy
    exact BoundaryAdmission.truncation_zero_of_le n hy.le

/-- Actual compact-test harmonicity and nonpositive exterior values imply the
maximum principle on any bounded open set, without boundary regularity. -/
theorem nonpos_of_compact_test_harmonic {D : Set Plane}
    (hD : IsOpen D) (hb : Bornology.IsBounded D) {u : Plane → ℝ}
    (hc : Continuous u) (hs : ContDiffOn ℝ ∞ u D)
    (hout : ∀ x ∉ D, u x ≤ 0)
    (hharm : ∀ ψ : Plane → ℝ, IsTest D ψ →
      (∫ x, inner (𝕜 := ℝ) (gradient u x) (gradient ψ x)) = 0) :
    ∀ x, u x ≤ 0 := by
  have htest (n : ℕ) := BoundaryAdmission.truncation_isTest_of_nonpos hD hb hc hs hout n
  have hgrad (n : ℕ) (x : Plane) (hx : x ∈ D) :
      gradient (fun y => BoundaryAdmission.truncation n (u y)) x =
        BoundaryAdmission.coefficient n (u x) • gradient u x := by
    have hd := ((hs x hx).contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
    have h := (BoundaryAdmission.truncation_hasDerivAt n (u x)).comp_hasFDerivAt x
      hd.hasGradientAt.hasFDerivAt
    apply HasGradientAt.gradient
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [Function.comp_def, map_smul, RCLike.conj_to_real] using h
  have hzero (n : ℕ) : (fun x => BoundaryAdmission.truncation n (u x)) = 0 := by
    let ψ : Plane → ℝ := fun x => BoundaryAdmission.truncation n (u x)
    have hp : IsTest D ψ := htest n
    have hi := classical_smooth_test_pairing_integrable hD hs hp
    have hn (x : Plane) : 0 ≤ inner (𝕜 := ℝ) (gradient u x) (gradient ψ x) := by
      by_cases hx : x ∈ D
      · rw [hgrad n x hx, real_inner_smul_right, real_inner_self_eq_norm_sq]
        exact mul_nonneg (SmoothPositivePart.slope_nonneg n _) (sq_nonneg _)
      · rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hx (hp.2.2 h))]
        simp
    have hpair : ∀ᵐ x ∂volume,
        inner (𝕜 := ℝ) (gradient u x) (gradient ψ x) = 0 :=
      (integral_eq_zero_iff_of_nonneg hn hi).mp (hharm ψ hp)
    have hg : gradient ψ =ᵐ[volume] 0 := by
      filter_upwards [hpair] with x hx
      by_cases hxD : x ∈ D
      · rw [hgrad n x hxD, real_inner_smul_right, real_inner_self_eq_norm_sq] at hx
        have hz := mul_eq_zero.mp hx
        rcases hz with hz | hz
        · change gradient (fun y => BoundaryAdmission.truncation n (u y)) x = 0
          rw [hgrad n x hxD, hz, zero_smul]
        · have hg0 : gradient u x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
          change gradient (fun y => BoundaryAdmission.truncation n (u y)) x = 0
          rw [hgrad n x hxD, hg0, smul_zero]
      · exact gradient_eq_zero_of_not_mem_tsupport (fun h => hxD (hp.2.2 h))
    exact Measure.eq_of_ae_eq (hp.memH10.value_ae_zero_of_gradient_ae_zero hb hg)
      hp.1.continuous continuous_const
  intro x
  apply le_of_not_gt
  intro hpos
  have hlim := BoundaryAdmission.truncation_tendsto hpos.le
  have hz : Tendsto (fun n => BoundaryAdmission.truncation n (u x)) atTop (𝓝 0) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) using 1
    funext n
    exact congrFun (hzero n) x
  exact hpos.ne' (tendsto_nhds_unique hlim hz)

/-- Translation differences of an actual weak torsion representative satisfy
an interior maximum principle. The exterior increment hypothesis supplies
only boundary data, and the Poisson forcings cancel on the common domain. -/
theorem IsWeakTorsion.translated_sub_le_of_exterior_bound
    {D : Set Plane} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : IsOpen D) (hb : Bornology.IsBounded D)
    (hc : Continuous U) (hs : ContDiffOn ℝ ∞ U D)
    (hgrad : g =ᵐ[volume.restrict D] gradient U)
    {a : Plane} {c : ℝ}
    (hout : ∀ x, x ∉ D ∨ x - a ∉ D → U (x - a) - U x ≤ c) :
    ∀ x, U (x - a) - U x ≤ c := by
  let E : Set Plane := ((fun z : Plane => z - a) ⁻¹' D) ∩ D
  have hE : IsOpen E := (hD.preimage (continuous_id.sub continuous_const)).inter hD
  have hsT : ContDiffOn ℝ ∞ (Torsion.translatedValue a U) E := by
    apply hs.comp (contDiff_id.sub contDiff_const).contDiffOn
    exact inter_subset_left
  have hsE := hsT.sub (hs.mono inter_subset_right)
  let w : Plane → ℝ := fun x => U (x - a) - U x - c
  have hsw : ContDiffOn ℝ ∞ w E := hsE.sub contDiffOn_const
  have hgradW (x : Plane) (hx : x ∈ E) :
      gradient w x = gradient U (x - a) - gradient U x := by
    have hd := ((hs x hx.2).contDiffAt (hD.mem_nhds hx.2)).differentiableAt (by simp)
    have hdT := ((hsT x hx).contDiffAt (hE.mem_nhds hx)).differentiableAt (by simp)
    have hd0 := ((hs (x-a) hx.1).contDiffAt (hD.mem_nhds hx.1)).differentiableAt (by simp)
    change gradient (fun y => Torsion.translatedValue a U y - U y - c) x = _
    unfold gradient
    rw [fderiv_sub_const, fderiv_fun_sub hdT hd, map_sub]
    exact congrArg₂ (fun v z : Plane => v - z) (gradient_translatedValue hd0) rfl
  have hga : ∀ᵐ x ∂volume, x ∈ D → g x = gradient U x :=
    (ae_restrict_iff' hD.measurableSet).mp hgrad
  have hgaT := (measurePreserving_sub_const a).quasiMeasurePreserving.ae hga
  have hharm := (hu.translatedValue hD.measurableSet a).difference_weakHarmonicOn hu
    (U := E) inter_subset_left inter_subset_right
  have hmax : ∀ x, w x ≤ 0 := by
    apply nonpos_of_compact_test_harmonic hE (hb.subset inter_subset_right)
      ((hc.comp (continuous_id.sub continuous_const)).sub hc |>.sub continuous_const) hsw
    · intro x hx
      apply sub_nonpos.mpr
      apply hout x
      by_cases hxD : x ∈ D
      · exact Or.inr (fun hxT => hx ⟨hxT, hxD⟩)
      · exact Or.inl hxD
    · intro ψ hψ
      rw [← hharm.2 ψ hψ]
      apply integral_congr_ae
      filter_upwards [hga, hgaT] with x hx hxT
      by_cases hxE : x ∈ E
      · change inner (𝕜 := ℝ) (gradient w x) (gradient ψ x) = _
        rw [hgradW x hxE, ← hx hxE.2, ← hxT hxE.1]
        rfl
      · rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hxE (hψ.2.2 h))]
        simp
  intro x
  exact sub_nonpos.mp (hmax x)

/-- A common bound on every sufficiently short increment propagates along
straight segments, with the same constant. -/
theorem lipschitzWith_of_small_increment {U : Plane → ℝ} {L : ℝ≥0} {δ : ℝ}
    (hδ : 0 < δ)
    (hinc : ∀ x a : Plane, ‖a‖ < δ → U (x + a) - U x ≤ L * ‖a‖) :
    LipschitzWith L U := by
  have hall (x y : Plane) : U y - U x ≤ L * ‖y - x‖ := by
    obtain ⟨n, hn⟩ := exists_nat_gt (max (‖y - x‖ / δ) 0)
    have hn0 : (0 : ℝ) < n := (le_max_right _ _).trans_lt hn
    have hnn : (n : ℝ) ≠ 0 := hn0.ne'
    let v : Plane := (n : ℝ)⁻¹ • (y - x)
    have hvnorm : ‖v‖ = ‖y - x‖ / n := by
      simp only [v, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn0, div_eq_mul_inv]
      ring
    have hv : ‖v‖ < δ := by
      rw [hvnorm, div_lt_iff₀ hn0]
      have hn' := (le_max_left _ _).trans_lt hn
      have hh := (div_lt_iff₀ hδ).mp hn'
      nlinarith
    have hsum (k : ℕ) : U (x + (k : ℝ) • v) - U x ≤ (k : ℝ) * (L * ‖v‖) := by
      induction k with
      | zero => simp
      | succ k ih =>
        have hi := hinc (x + (k : ℝ) • v) v hv
        have heq : x + ((k + 1 : ℕ) : ℝ) • v = (x + (k : ℝ) • v) + v := by
          simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
          abel
        rw [heq]
        push_cast
        linarith
    have hnv : (n : ℝ) • v = y - x := by
      simp only [v, smul_smul, mul_inv_cancel₀ hnn, one_smul]
    have hh := hsum n
    rw [hnv, add_sub_cancel] at hh
    calc
      U y - U x ≤ (n : ℝ) * (L * ‖v‖) := hh
      _ = L * ‖y - x‖ := by rw [hvnorm]; field_simp
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  constructor
  · have h := hall x y
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  · simpa only [dist_eq_norm] using hall y x

/-- A uniform boundary collar distance estimate implies a global Lipschitz
bound on the actual weak torsion representative. The domain may be irregular
and need not be convex. The collar can have any positive width. -/
theorem IsWeakTorsion.lipschitzWith_of_boundary_collar
    {D : Set Plane} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : IsOpen D) (hb : Bornology.IsBounded D)
    (hc : Continuous U) (hs : ContDiffOn ℝ ∞ U D)
    (hgrad : g =ᵐ[volume.restrict D] gradient U)
    (hzero : ∀ x ∉ D, U x = 0) (hpos : ∀ x, 0 ≤ U x)
    {L : ℝ≥0} {δ : ℝ} (hδ : 0 < δ)
    (hcollar : ∀ x ∈ D, Metric.infDist x Dᶜ < δ →
      U x ≤ L * Metric.infDist x Dᶜ) :
    LipschitzWith L U := by
  apply lipschitzWith_of_small_increment hδ
  intro x v hv
  have htrans := hu.translated_sub_le_of_exterior_bound hD hb hc hs hgrad
    (a := -v) (c := L * ‖v‖) ?_
  · simpa only [sub_neg_eq_add] using htrans x
  intro z hz
  rcases hz with hz | hz
  · have hz0 := hzero z hz
    have hbound : U (z + v) ≤ L * ‖v‖ := by
      by_cases hy : z + v ∈ D
      · have hd : Metric.infDist (z + v) Dᶜ ≤ ‖v‖ := by
          convert Metric.infDist_le_dist_of_mem (show z ∈ Dᶜ from hz) using 1
          simp [dist_eq_norm]
        exact (hcollar (z + v) hy (hd.trans_lt hv)).trans
          (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
      · rw [hzero (z + v) hy]
        exact mul_nonneg L.coe_nonneg (norm_nonneg _)
    simpa only [sub_neg_eq_add, hz0, sub_zero] using hbound
  · rw [hzero (z - -v) hz]
    simpa only [zero_sub] using (neg_nonpos.mpr (hpos z)).trans
      (mul_nonneg L.coe_nonneg (norm_nonneg v))

/-- Arbitrarily small losses in uniform collar bounds disappear in the global
Lipschitz constant. Each loss may use its own positive collar width. -/
theorem IsWeakTorsion.lipschitzWith_of_boundary_collar_approx
    {D : Set Plane} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : IsOpen D) (hb : Bornology.IsBounded D)
    (hc : Continuous U) (hs : ContDiffOn ℝ ∞ U D)
    (hgrad : g =ᵐ[volume.restrict D] gradient U)
    (hzero : ∀ x ∉ D, U x = 0) (hpos : ∀ x, 0 ≤ U x)
    {L : ℝ≥0}
    (hcollar : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ D, Metric.infDist x Dᶜ < δ →
        U x ≤ (L + ε : ℝ≥0) * Metric.infDist x Dᶜ) :
    LipschitzWith L U := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_forall_pos_le_add
  intro ε hε
  let η : ℝ≥0 := ⟨ε / (dist x y + 1), div_nonneg hε.le (by positivity)⟩
  have hη : 0 < η := by
    change 0 < ε / (dist x y + 1)
    exact div_pos hε (by positivity)
  obtain ⟨δ, hδ, hcδ⟩ := hcollar η hη
  have hLip := hu.lipschitzWith_of_boundary_collar hD hb hc hs hgrad hzero hpos hδ hcδ
  have hh := hLip.dist_le_mul x y
  have hηeq : (η : ℝ) * (dist x y + 1) = ε := by
    change ε / (dist x y + 1) * (dist x y + 1) = ε
    exact div_mul_cancel₀ _ (by positivity)
  simp only [NNReal.coe_add] at hh
  have hη0 := η.coe_nonneg
  nlinarith

end Torsion

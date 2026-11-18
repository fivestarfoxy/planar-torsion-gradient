module

public import Torsion.WeakTranslationLipschitz
public import Torsion.SlabTorsionBarrier
public import Mathlib.Topology.Algebra.Indicator

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Comparison with a harmonic correction on a bounded subdomain -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace Torsion

/-- A continuous function with zero compact-test Laplacian is bounded by
its boundary values. Only its positive part on the open set is needed in
the zero-extension maximum principle. -/
theorem nonpos_on_of_compact_test_harmonic_frontier {S : Set Plane}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) {w : Plane → ℝ}
    (hc : Continuous w) (hs : ContDiffOn ℝ ∞ w S)
    (hfront : ∀ x ∈ frontier S, w x ≤ 0)
    (hharm : ∀ ψ : Plane → ℝ, IsTest S ψ →
      (∫ x, inner (𝕜 := ℝ) (gradient w x) (gradient ψ x)) = 0) :
    ∀ x ∈ S, w x ≤ 0 := by
  classical
  let V := S.indicator (fun z => max (w z) 0)
  let P := S ∩ {z | 0 < w z}
  have hopen : IsOpen P := hS.inter (isOpen_lt continuous_const hc)
  have hP : P ⊆ S := inter_subset_left
  have hcont : Continuous V := continuous_indicator
    (fun x hx => max_eq_right (hfront x hx)) (hc.max continuous_const).continuousOn
  have heq : EqOn V w P := fun x hx => by
    change S.indicator (fun z => max (w z) 0) x = w x
    rw [indicator_of_mem hx.1, max_eq_left hx.2.le]
  have hpos := nonpos_of_compact_test_harmonic hopen (hb.subset hP) hcont
    ((hs.mono hP).congr heq) (fun x hx => by
      by_cases hxS : x ∈ S
      · have hn : w x ≤ 0 := le_of_not_gt (fun hw => hx ⟨hxS, hw⟩)
        simp [V, hxS, max_eq_right hn]
      · simp [V, hxS]) (fun ψ hψ => by
        rw [← hharm ψ (hψ.mono hP)]
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : z ∈ P
        · have hnear : V =ᶠ[𝓝 z] w := Filter.mem_of_superset (hopen.mem_nhds hz) (fun _ hy => heq hy)
          change inner (𝕜 := ℝ) (gradient V z) _ = _
          simp only [gradient, hnear.fderiv_eq]
        · rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hz (hψ.2.2 h))]
          simp)
  intro x hx
  exact (le_max_left _ 0).trans (by simpa only [V, indicator_of_mem hx] using hpos x)

/-- Comparison on a subdomain against a slab solution minus an arbitrary
smooth harmonic function. The forcing cancels in the weak equation. -/
theorem IsWeakTorsion.le_slab_sub_harmonic_on {D S : Set Plane}
    {u U : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D u g)
    (hD : IsOpen D) (hS : IsOpen S) (hb : Bornology.IsBounded S) (hSD : S ⊆ D)
    (hc : Continuous U) (hs : ContDiffOn ℝ ∞ U D)
    (hg : g =ᵐ[volume.restrict D] gradient U)
    (B : ℝ) {H : Plane → ℝ} (hH : ContDiff ℝ ∞ H)
    (hlap : ∀ x, WeakHarmonicRegularity.planarLaplacian H x = 0)
    (hfront : ∀ x ∈ frontier S, U x + H x ≤ slabTorsionBarrier 0 B x) :
    ∀ x ∈ S, U x + H x ≤ slabTorsionBarrier 0 B x := by
  let V := slabTorsionBarrier 0 B
  let w (z : Plane) := U z + H z - V z
  have hV : ContDiff ℝ ∞ V := slabTorsionBarrier_contDiff _ _
  have hw : ContDiffOn ℝ ∞ w S := ((hs.mono hSD).add hH.contDiffOn).sub hV.contDiffOn
  have hmax : ∀ z ∈ S, w z ≤ 0 := by
    apply nonpos_on_of_compact_test_harmonic_frontier hS hb
      ((hc.add hH.continuous).sub hV.continuous) hw
      (fun x hx => sub_nonpos.mpr (hfront x hx))
    intro ψ hψ
    let pair (F : Plane → Plane) := fun x => inner (𝕜 := ℝ) (F x) (gradient ψ x)
    have hUh := classical_smooth_test_pairing_integrable hS (hs.mono hSD) hψ
    have hHh := classical_smooth_test_pairing_integrable hS hH.contDiffOn hψ
    have hVh := classical_smooth_test_pairing_integrable hS hV.contDiffOn hψ
    have hUeq : (∫ x, pair (gradient U) x) = ∫ x, ψ x := by
      rw [← hu.global_smooth_test_equation (hψ.mono hSD)]
      apply integral_congr_ae
      filter_upwards [(ae_restrict_iff' hD.measurableSet).mp hg] with x h
      by_cases hx : x ∈ D
      · change inner (𝕜 := ℝ) (gradient U x) _ = _
        rw [← h hx]
      · have hz := gradient_eq_zero_of_not_mem_tsupport (fun h => hx (hSD (hψ.2.2 h)))
        simp only [pair, hz, inner_zero_right]
    have hHeq := classical_harmonic_smooth_test_equation hS hH.contDiffOn (fun x _ => hlap x) hψ
    have hVeq := classical_poisson_smooth_test_equation hS hV.contDiffOn
      (fun x _ => slabTorsionBarrier_laplacian 0 B x) hψ
    have hpair : pair (gradient w) = fun x =>
        pair (gradient U) x + pair (gradient H) x - pair (gradient V) x := by
      funext x
      by_cases hx : x ∈ S
      · have hUd := ((hs _ (hSD hx)).contDiffAt (hD.mem_nhds (hSD hx))).differentiableAt (by simp)
        have hHd := hH.differentiable (by simp) x
        have hVd := hV.differentiable (by simp) x
        have hderiv : gradient w x = gradient U x + gradient H x - gradient V x := by
          change gradient (fun z => (U z + H z) - V z) x = _
          unfold gradient
          rw [fderiv_fun_sub (f := fun z => U z + H z) (hUd.add hHd) hVd, fderiv_fun_add hUd hHd, map_sub, map_add]
        change inner (𝕜 := ℝ) (gradient w x) _ = _
        rw [hderiv, inner_sub_left, inner_add_left]
      · have hz := gradient_eq_zero_of_not_mem_tsupport (fun h => hx (hψ.2.2 h))
        simp only [pair, hz, inner_zero_right, add_zero, sub_zero]
    change (∫ x, pair (gradient w) x) = 0
    rw [hpair]
    change (∫ x, ((pair (gradient U) + pair (gradient H)) x - pair (gradient V) x)) = 0
    have h1 : Integrable (pair (gradient U)) volume := hUh
    have h2 : Integrable (pair (gradient H)) volume := hHh
    have h3 : Integrable (pair (gradient V)) volume := hVh
    rw [integral_sub (h1.add h2) h3]
    simp only [Pi.add_apply]
    rw [integral_add h1 h2, hUeq]
    change (∫ x, ψ x) + (∫ x, inner (𝕜 := ℝ) (gradient H x) (gradient ψ x)) -
        (∫ x, inner (𝕜 := ℝ) (gradient V x) (gradient ψ x)) = 0
    rw [hHeq, hVeq]
    ring
  exact fun x hx => sub_nonpos.mp (hmax x hx)

end Torsion

import Torsion.CauchyConformalGeometry.ExteriorBoundary
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Arbitrary physical approaches to the finite Cauchy boundary

The actual Cauchy inverse tends to the corresponding finite boundary
parameter along every interior physical approach. Decay excludes escaping
preimages; compactness and finite boundary injectivity exclude all other
limit points. No inverse boundary extension is assumed.
-/
noncomputable section
open Set Filter MeasureTheory Metric Bornology
open scoped Topology NNReal

namespace Torsion.Spectral

private theorem cauchy_uniform_decay {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R < ‖z‖ → ‖cauchy φ z‖ < ε := by
  have hlim : Tendsto (cauchy φ) (cobounded ℂ) (𝓝 0) :=
    cauchy_tendsto_zero hφ tendsto_norm_cobounded_atTop
  have hev : ∀ᶠ z in cobounded ℂ, ‖cauchy φ z‖ < ε := by
    simpa only [mem_ball, dist_zero_right] using hlim.eventually (ball_mem_nhds (0 : ℂ) hε)
  obtain ⟨R, _, hR⟩ := (Filter.hasBasis_cobounded_norm (E := ℂ)).mem_iff.mp hev
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  exact hR ((le_max_left R 1).trans hz.le)

/-- Preimages of physical points near a nonzero boundary target remain
in a fixed finite parameter ball, by actual Cauchy decay at infinity. -/
theorem cauchyInverse_bounded_near_nonzero {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {p : ℂ} (hp : p ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ w ∈ ball p (‖p‖ / 2) ∩ cauchyImage φ,
      ‖cauchyInverse φ w‖ ≤ R := by
  have hpε : 0 < ‖p‖ / 2 := half_pos (norm_pos_iff.2 hp)
  obtain ⟨R, hR, hdecay⟩ := cauchy_uniform_decay hφ hpε
  refine ⟨R, hR, ?_⟩
  rintro w ⟨hwball, hw⟩
  by_contra! hnorm
  have hsmall := hdecay (cauchyInverse φ w) hnorm
  rw [cauchy_cauchyInverse hw] at hsmall
  have hdist : ‖w - p‖ < ‖p‖ / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hwball
  have htri : ‖p‖ ≤ ‖w - p‖ + ‖w‖ := by
    have ht := norm_sub_le w (w - p)
    simpa only [sub_sub_cancel, add_comm] using ht
  linarith

/-- The only closed-half-plane preimage of a finite boundary value is its
actual real parameter. Interior preimages are excluded by the proved
frontier theorem, and finite boundary preimages by injectivity. -/
theorem cauchyExtension_preimage_boundary {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {z : ℂ} (hz : z ∈ closure upperHalfPlane) (t : ℝ)
    (heq : cauchyExtension φ z = cauchyExtension φ (t : ℂ)) : z = (t : ℂ) := by
  have hc := hφ.continuous hα0
  have him : 0 ≤ z.im := by
    simpa only [upperHalfPlane, Complex.closure_setOf_lt_im, mem_setOf_eq] using hz
  have hz0 : z.im = 0 := by
    by_contra hne
    have hzH : z ∈ upperHalfPlane := lt_of_le_of_ne him (Ne.symm hne)
    apply cauchyExtension_ofReal_not_mem_image hc hodd hzero hpos t
    refine ⟨z, hzH, ?_⟩
    exact (cauchyExtension_eq hc.continuousOn hzH).symm.trans heq
  have hzreal : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz0]
  have hre : z.re = t :=
    cauchy_boundary_injective hφ hα0 hα1 hodd hzero hpos (by simpa only [hzreal] using heq)
  exact hzreal.symm.trans (congrArg Complex.ofReal hre)

/-- The actual conformal inverse has the finite boundary limit along
arbitrary physical interior approaches, including the two junctions. -/
theorem cauchyInverse_boundary_tendsto {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) (t : ℝ) :
    Tendsto (cauchyInverse φ)
      (𝓝[cauchyImage φ] (cauchyExtension φ (t : ℂ))) (𝓝 (t : ℂ)) := by
  let p : ℂ := cauchyExtension φ (t : ℂ)
  have hc := hφ.continuous hα0
  have hp : p ≠ 0 := cauchy_boundary_ne_zero hφ hα0 hα1 hodd hzero hpos t
  have hpε : 0 < ‖p‖ / 2 := half_pos (norm_pos_iff.2 hp)
  obtain ⟨R, _, hbound⟩ := cauchyInverse_bounded_near_nonzero hc.continuousOn hp
  let K : Set ℂ := closure upperHalfPlane ∩ closedBall 0 R
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).inter_left isClosed_closure
  have hF : ContinuousOn (cauchyExtension φ) (closure upperHalfPlane) :=
    (cauchy_extensions_diffContOnCl_of_holder hφ hα0 hα1 hodd hzero).1.continuousOn
  apply _root_.tendsto_nhds.mpr
  intro U hU htU
  have hbad : IsCompact (K \ U) := hK.diff hU
  have hbadclosed : IsClosed (cauchyExtension φ '' (K \ U)) :=
    (hbad.image_of_continuousOn (hF.mono (fun _ hz => hz.1.1))).isClosed
  have hpnot : p ∉ cauchyExtension φ '' (K \ U) := by
    rintro ⟨z, hz, hzp⟩
    have hzt : z = (t : ℂ) :=
      cauchyExtension_preimage_boundary hφ hα0 hα1 hodd hzero hpos hz.1.1 t hzp
    exact hz.2 (hzt.symm ▸ htU)
  have hnb : (cauchyExtension φ '' (K \ U))ᶜ ∈ 𝓝 p :=
    hbadclosed.isOpen_compl.mem_nhds hpnot
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p hpε),
    mem_nhdsWithin_of_mem_nhds hnb, self_mem_nhdsWithin] with w hwball hwnot hw
  change cauchyInverse φ w ∈ U
  have hzinK : cauchyInverse φ w ∈ K := by
    refine ⟨subset_closure (cauchyInverse_mem hw), ?_⟩
    simpa only [mem_closedBall, dist_zero_right] using hbound w ⟨hwball, hw⟩
  by_contra hnot
  apply hwnot
  refine ⟨cauchyInverse φ w, ⟨hzinK, hnot⟩, ?_⟩
  exact (cauchyExtension_eq hc.continuousOn (cauchyInverse_mem hw)).trans
    (cauchy_cauchyInverse hw)

/-- The same inverse limit retains membership in the parameter half-plane. -/
theorem cauchyInverse_boundary_tendsto_within {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) (t : ℝ) :
    Tendsto (cauchyInverse φ)
      (𝓝[cauchyImage φ] (cauchyExtension φ (t : ℂ))) (𝓝[upperHalfPlane] (t : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨cauchyInverse_boundary_tendsto hφ hα0 hα1 hodd hzero hpos t, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact cauchyInverse_mem hw

/-- Any actual parameter-side boundary limit transfers to arbitrary
physical interior approaches through the proved inverse boundary limit. -/
theorem tendsto_physical_boundary_of_cauchy_comp {E : Type*} [TopologicalSpace E]
    {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) (t : ℝ) {f : ℂ → E} {L : E}
    (hlim : Tendsto (fun z => f (cauchy φ z)) (𝓝[upperHalfPlane] (t : ℂ)) (𝓝 L)) :
    Tendsto f (𝓝[cauchyImage φ] (cauchyExtension φ (t : ℂ))) (𝓝 L) := by
  have h := hlim.comp (cauchyInverse_boundary_tendsto_within hφ hα0 hα1 hodd hzero hpos t)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact congrArg f (cauchy_cauchyInverse hw)

end Torsion.Spectral

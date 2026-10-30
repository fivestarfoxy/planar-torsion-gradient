module

public import Torsion.MarkedBoundaryRegularity
public import Torsion.ClassicalWeakTorsion
public import Torsion.GradientBoundExhaustion

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Interior representatives and Lipschitz bounds for actual weak torsion

The original weak solution has a smooth value and gradient representative
on every sufficiently small interior ball. Consequently a Lipschitz
representative bounds the actual weak gradient, rather than a separately
postulated classical gradient.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace Torsion

/-- A compact quadratic correction turns the actual torsion pair into a
genuine globally admissible pair harmonic on the original bounded domain. -/
theorem IsWeakTorsion.exists_interior_harmonic_correction
    {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hb : Bornology.IsBounded D) :
    ∃ p : Plane → ℝ, IsTest univ p ∧
      (∀ x ∈ D, p =ᶠ[𝓝 x] quadraticIm) ∧
      MemH10 univ (fun x => u x + p x) (fun x => g x + gradient p x) ∧
      IsWeakHarmonicOn D (fun x => u x + p x) (fun x => g x + gradient p x) := by
  obtain ⟨η, hη, hone⟩ := exists_test_eq_one_near_compact isOpen_univ
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)
    (subset_univ (closure D))
  let p : Plane → ℝ := fun x => η x * quadraticIm x
  have hp : IsTest univ p := hη.mul_left quadraticIm_contDiff
  have hpnear (x : Plane) (hx : x ∈ D) : p =ᶠ[𝓝 x] quadraticIm := by
    have heq := hone.filter_mono (nhds_le_nhdsSet (subset_closure hx))
    filter_upwards [heq] with y hy
    simp only [p, hy, one_mul]
  have hmem := (hu.1.mono (subset_univ D)).add hp.memH10
  refine ⟨p, hp, hpnear, hmem, hmem.distributionalGradient, ?_⟩
  intro ψ hψ
  have hpde := hψ.quadraticIm_pairing
  have hpgrad (x : Plane) (hx : x ∈ D) :
      gradient p x = (x.im : ℂ) * Complex.I := by
    rw [(hpnear x hx).gradient_eq, gradient_quadraticIm]
  have heq : (∫ x, inner (𝕜 := ℝ) (gradient p x) (gradient ψ x)) =
      -(∫ x, ψ x) := by
    rw [← hpde]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      by_cases hx : x ∈ D
      · rw [hpgrad x hx]
      · rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hx (hψ.2.2 h))]
        simp
  have hi := integrable_real_inner_of_memLp_two hu.1.2.1 (hψ.memLp_gradient (p := 2))
  have hj := integrable_real_inner_of_memLp_two hp.memH10.2.1 (hψ.memLp_gradient (p := 2))
  simp only [inner_add_left]
  rw [integral_add hi hj, hu.global_smooth_test_equation hψ, heq, add_neg_cancel]

/-- Genuine interior smoothness of the original value and weak gradient.
No boundary regularity is required. -/
theorem IsWeakTorsion.exists_smooth_interior_representative
    {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : IsOpen D) (hb : Bornology.IsBounded D)
    {x : Plane} (hx : x ∈ D) :
    ∃ (r : ℝ) (v : Plane → ℝ), 0 < r ∧ ContDiff ℝ ∞ v ∧
      Metric.ball x r ⊆ D ∧
      (u =ᵐ[volume.restrict (Metric.ball x r)] v) ∧
      (g =ᵐ[volume.restrict (Metric.ball x r)] gradient v) := by
  obtain ⟨p, hp, hpnear, hmem, hw⟩ := hu.exists_interior_harmonic_correction hb
  obtain ⟨R, hR, hRD⟩ := Metric.isOpen_iff.mp hD x hx
  let s := R / 8
  have hs : 0 < s := by dsimp [s]; positivity
  have hsR : 4 * s ≤ R := by dsimp [s]; linarith
  obtain ⟨v, hv, hvAE, hgAE⟩ := hw.exists_smoothRepresentative_on_ball hmem hs
    ((Metric.ball_subset_ball hsR).trans hRD)
  let V : Plane → ℝ := fun y => v y - p y
  have hV : ContDiff ℝ ∞ V := hv.sub hp.1
  have hVG (y : Plane) : gradient V y = gradient v y - gradient p y := by
    unfold gradient
    rw [fderiv_sub (hv.differentiable (by simp) y)
      (hp.1.differentiable (by simp) y), map_sub]
  refine ⟨s / 2, V, half_pos hs, hV, ?_, ?_, ?_⟩
  · apply (Metric.ball_subset_ball ?_).trans hRD
    dsimp [s]
    linarith
  · filter_upwards [hvAE] with y hy
    dsimp [V]
    linarith
  · filter_upwards [hgAE] with y hy
    rw [hVG, ← hy, add_sub_cancel_right]

/-- A Lipschitz representative controls the original interior weak gradient.
The actual weak and classical gradients are identified locally by Weyl
regularity; a countable open subcover passes the bound to the whole domain. -/
theorem IsWeakTorsion.gradient_ae_bound_of_lipschitzOn
    {D : Set Plane} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : IsOpen D) (hb : Bornology.IsBounded D)
    {L : ℝ≥0} (hU : LipschitzOnWith L U D)
    (hrep : u =ᵐ[volume.restrict D] U) :
    ∀ᵐ x ∂volume.restrict D, ‖g x‖ ≤ L := by
  classical
  have hlocal (x : D) := hu.exists_smooth_interior_representative hD hb x.2
  choose r v hr hv hball hvalue hgrad using hlocal
  let W (x : D) : Set Plane := Metric.ball (x : Plane) (r x)
  have hWopen (x : D) : IsOpen (W x) := Metric.isOpen_ball
  have hcover : (⋃ x : D, W x) = D := by
    apply Subset.antisymm
    · exact iUnion_subset hball
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨S, hS, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWopen
  rw [← hcover, ← hSU]
  apply (ae_restrict_biUnion_iff W hS _).mpr
  intro x _hx
  have heqAE : v x =ᵐ[volume.restrict (W x)] U :=
    (hvalue x).symm.trans (ae_restrict_of_ae_restrict_of_subset (hball x) hrep)
  have heq : EqOn (v x) U (W x) := Measure.eqOn_open_of_ae_eq heqAE
    (hWopen x) (hv x).continuous.continuousOn
    (hU.continuousOn.mono (hball x))
  have hLip : LipschitzOnWith L (v x) (W x) :=
    fun y hy z hz => by
      rw [heq hy, heq hz]
      exact hU (hball x hy) (hball x hz)
  filter_upwards [hgrad x, ae_restrict_mem (hWopen x).measurableSet] with y hy hyW
  rw [hy]
  change ‖(InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ (v x) y)‖ ≤ L
  rw [LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitzOn ℝ ((hWopen x).mem_nhds hyW) hLip

/-- The bound is on the original essential supremum used in the optimization
problem, and needs only a Lipschitz representative of the actual solution. -/
theorem IsWeakTorsion.eLpNorm_gradient_le_of_lipschitzOn
    {D : Set Plane} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : IsOpen D) (hb : Bornology.IsBounded D)
    {L : ℝ≥0} (hU : LipschitzOnWith L U D)
    (hrep : u =ᵐ[volume.restrict D] U) :
    eLpNorm g ∞ (volume.restrict D) ≤ (L : ℝ≥0∞) := by
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [hu.gradient_ae_bound_of_lipschitzOn hD hb hU hrep] with x hx
  exact_mod_cast hx

end Torsion

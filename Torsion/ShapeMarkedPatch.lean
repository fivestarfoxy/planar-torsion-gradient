module

public import Torsion.ShapeGradient
public import Torsion.MarkedBoundaryRegularity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# One fixed genuine marked patch for localized deformations

A deformation field supported in the upper half-plane fixes its complement.
Injectivity therefore preserves the half-plane. If it vanishes near the
marked point, every homeomorphism realizing `id+tV` fixes one common full
ball, including its inverse and differential. The original and deformed
domains have exactly the same marked half-ball for every such parameter.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Torsion.Shape

theorem deformation_eq_of_zero {V : Plane → Plane} {z : Plane} (hz : V z = 0) (t : ℝ) :
    deformation V t z = z := by simp [deformation, hz]

/-- Local vanishing is actual neighborhood equality with the identity,
so the real differential is exactly the identity as well. -/
theorem deformation_eventuallyEq_id_of_zero_on_ball {V : Plane → Plane} {R : ℝ}
    (hzero : ∀ z ∈ Metric.ball (0 : Plane) R, V z = 0) (t : ℝ)
    {z : Plane} (hz : z ∈ Metric.ball (0 : Plane) R) :
    deformation V t =ᶠ[𝓝 z] id := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  exact deformation_eq_of_zero (hzero w hw) t

theorem homeomorph_symm_eq_of_fix {e : Plane ≃ₜ Plane} {z : Plane} (hz : e z = z) :
    e.symm z = z := by
  apply e.injective
  rw [e.apply_symm_apply, hz]

/-- A homeomorphism equal to the identity on a neighborhood has the actual
identity pullback of every value and every weak-gradient field there. -/
theorem gradientPullback_eq_of_eventuallyEq_id {e : Plane ≃ₜ Plane} {z : Plane}
    (he : (e : Plane → Plane) =ᶠ[𝓝 z] id) (g : Plane → Plane) :
    gradientPullback e g z = g z := by
  unfold gradientPullback
  rw [he.fderiv_eq, fderiv_id, he.self_of_nhds]
  simp

/-- Fixed points on a full ball prevent any exterior point from entering
that ball, by actual injectivity. Thus image-domain membership is unchanged
there, without an assumed inverse-locality property. -/
theorem image_inter_ball_eq_of_fix {e : Plane ≃ₜ Plane} {D : Set Plane} {R : ℝ}
    (he : ∀ z ∈ Metric.ball (0 : Plane) R, e z = z) :
    e '' D ∩ Metric.ball (0 : Plane) R = D ∩ Metric.ball (0 : Plane) R := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, hxz⟩, hz⟩
    have hxz' : x = z := e.injective (hxz.trans (he z hz).symm)
    exact ⟨hxz' ▸ hx, hz⟩
  · rintro ⟨hzD, hz⟩
    exact ⟨⟨z, hzD, he z hz⟩, hz⟩

/-- An actual deformation supported above the real axis preserves the
upper half-plane whenever it is a homeomorphism. No small-parameter or
boundary-sign assumption is inserted. -/
theorem deformation_image_subset_upperHalfPlane {V : Plane → Plane}
    (hVU : tsupport V ⊆ upperHalfPlane) {D : Set Plane} (hDH : D ⊆ upperHalfPlane)
    (t : ℝ) (e : Plane ≃ₜ Plane) (he : (e : Plane → Plane) = deformation V t) :
    e '' D ⊆ upperHalfPlane := by
  rintro z ⟨x, hx, rfl⟩
  by_contra hn
  have hnot : e x ∉ tsupport V := fun h => hn (hVU h)
  have hfix : e (e x) = e x := by
    calc
      e (e x) = deformation V t (e x) := congrFun he (e x)
      _ = e x := deformation_eq_of_zero (image_eq_zero_of_notMem_tsupport hnot) t
  have hxx : e x = x := e.injective hfix
  exact hn (by simpa only [hxx] using hDH hx)

/-- A bounded original domain has bounded image under the actual global
homeomorphism, using compactness of its Euclidean closure. -/
theorem image_isBounded_of_homeomorph {D : Set Plane} (hD : Bornology.IsBounded D)
    (e : Plane ≃ₜ Plane) : Bornology.IsBounded (e '' D) := by
  have hc := Metric.isCompact_of_isClosed_isBounded isClosed_closure hD.closure
  exact (hc.image e.continuous).isBounded.subset (image_mono subset_closure)

/-- A single fixed physical half-ball for the original and every localized
deformed domain. The radius is chosen before the parameter and before any
homeomorphism used to realize the deformation. -/
theorem exists_fixed_marked_patch_with_zero {D : Set Plane} (hD : IsMarked D)
    {V : Plane → Plane} (hVU : tsupport V ⊆ upperHalfPlane)
    (hzero : V =ᶠ[𝓝 (0 : Plane)] (fun _ => 0)) :
    ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ Metric.ball (0 : Plane) (4 * r), V =ᶠ[𝓝 z] (fun _ => 0)) ∧
      ∀ (t : ℝ) (e : Plane ≃ₜ Plane),
      (e : Plane → Plane) = deformation V t →
      IsMarked (e '' D) ∧
      upperHalfPlane ∩ Metric.ball (0 : Plane) (4 * r) ⊆ D ∧
      upperHalfPlane ∩ Metric.ball (0 : Plane) (4 * r) ⊆ e '' D ∧
      ∀ z ∈ Metric.ball (0 : Plane) (4 * r),
        ((e : Plane → Plane) =ᶠ[𝓝 z] id) ∧ e.symm z = z ∧
        fderiv ℝ (e : Plane → Plane) z = ContinuousLinearMap.id ℝ Plane ∧
        (∀ g : Plane → Plane, gradientPullback e g z = g z) ∧
        (∀ u : Plane → ℝ, (u ∘ e) z = u z) := by
  obtain ⟨R, hR, hflat⟩ := hD.2.2.2
  obtain ⟨s, hs, hs0⟩ := Metric.eventually_nhds_iff.mp hzero
  let r : ℝ := min R s / 8
  have hr : 0 < r := by dsimp [r]; positivity
  have h4R : 4 * r ≤ R := by dsimp [r]; linarith [min_le_left R s]
  have h4s : 4 * r < s := by dsimp [r]; linarith [min_le_right R s]
  have hbase : upperHalfPlane ∩ Metric.ball (0 : Plane) (4 * r) ⊆ D := by
    intro z hz
    have hzR : z ∈ upperHalfPlane ∩ Metric.ball (0 : Plane) R :=
      ⟨hz.1, Metric.ball_subset_ball h4R hz.2⟩
    rw [← hflat] at hzR
    exact hzR.1
  have hzball : ∀ z ∈ Metric.ball (0 : Plane) (4 * r), V z = 0 := by
    intro z hz
    exact hs0 (Metric.mem_ball.mp (Metric.ball_subset_ball h4s.le hz))
  refine ⟨r, hr, ?_, ?_⟩
  · intro z hz
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact hzball w hw
  · intro t e he
    have heN {z : Plane} (hz : z ∈ Metric.ball (0 : Plane) (4 * r)) :
        (e : Plane → Plane) =ᶠ[𝓝 z] id := by
      rw [he]
      exact deformation_eventuallyEq_id_of_zero_on_ball hzball t hz
    have hepoint : ∀ z ∈ Metric.ball (0 : Plane) (4 * r), e z = z :=
      fun z hz => (heN hz).self_of_nhds
    have hsame := image_inter_ball_eq_of_fix (D := D) hepoint
    have himage : IsMarked (e '' D) := by
      refine ⟨e.isOpenMap D hD.1, image_isBounded_of_homeomorph hD.2.1 e,
        deformation_image_subset_upperHalfPlane hVU hD.2.2.1 t e he,
        4 * r, by positivity, ?_⟩
      rw [hsame]
      ext z
      constructor
      · exact fun hz => ⟨hD.2.2.1 hz.1, hz.2⟩
      · exact fun hz => ⟨hbase hz, hz.2⟩
    refine ⟨himage, hbase, ?_, ?_⟩
    · intro z hz
      exact ⟨z, hbase hz, hepoint z hz.2⟩
    · intro z hz
      refine ⟨heN hz, homeomorph_symm_eq_of_fix (hepoint z hz), ?_,
        fun g => gradientPullback_eq_of_eventuallyEq_id (heN hz) g, ?_⟩
      · rw [(heN hz).fderiv_eq, fderiv_id]
      · intro u
        simp only [Function.comp_apply, hepoint z hz]

/-- The original fixed-patch interface, retained with exactly its original
type. The stronger companion also retains vanishing of the displacement
on the selected patch for subsequent fixed-kernel identifications. -/
theorem exists_fixed_marked_patch {D : Set Plane} (hD : IsMarked D)
    {V : Plane → Plane} (hVU : tsupport V ⊆ upperHalfPlane)
    (hzero : V =ᶠ[𝓝 (0 : Plane)] (fun _ => 0)) :
    ∃ r : ℝ, 0 < r ∧ ∀ (t : ℝ) (e : Plane ≃ₜ Plane),
      (e : Plane → Plane) = deformation V t →
      IsMarked (e '' D) ∧
      upperHalfPlane ∩ Metric.ball (0 : Plane) (4 * r) ⊆ D ∧
      upperHalfPlane ∩ Metric.ball (0 : Plane) (4 * r) ⊆ e '' D ∧
      ∀ z ∈ Metric.ball (0 : Plane) (4 * r),
        ((e : Plane → Plane) =ᶠ[𝓝 z] id) ∧ e.symm z = z ∧
        fderiv ℝ (e : Plane → Plane) z = ContinuousLinearMap.id ℝ Plane ∧
        (∀ g : Plane → Plane, gradientPullback e g z = g z) ∧
        (∀ u : Plane → ℝ, (u ∘ e) z = u z) := by
  obtain ⟨r, hr, _, hpatch⟩ := exists_fixed_marked_patch_with_zero hD hVU hzero
  exact ⟨r, hr, hpatch⟩

end Torsion.Shape

module

public import Torsion.PhysicalCauchyGreenWeak
public import Torsion.PhysicalCauchyHarmonicBoundary

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Zero trace of the actual Green kernel on the entire physical boundary

The normalized logarithmic quotient decays at parameter infinity. The
proved escape of inverse coordinates therefore handles arbitrary physical
approaches to the marked point, completing the finite-parameter traces.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace Torsion.HalfPlane

theorem green_tendsto_zero_of_norm_tendsto {ι : Type*} {l : Filter ι}
    {z : ι → Plane} (hz : Tendsto (fun i => ‖z i‖) l atTop) (w : Plane) :
    Tendsto (fun i => green (z i) w) l (𝓝 0) := by
  have hi : Tendsto (fun i => (z i)⁻¹) l (𝓝 (0 : Plane)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_inv] using tendsto_inv_atTop_zero.comp hz
  have ha : Tendsto (fun i => 1 - star w * (z i)⁻¹) l (𝓝 (1 : Plane)) := by
    simpa using tendsto_const_nhds.sub (hi.const_mul (star w))
  have hb : Tendsto (fun i => 1 - w * (z i)⁻¹) l (𝓝 (1 : Plane)) := by
    simpa using tendsto_const_nhds.sub (hi.const_mul w)
  have hlog := ((ha.norm.log (by simp)).sub (hb.norm.log (by simp))).div_const (2 * Real.pi)
  simp only [norm_one, Real.log_one, sub_self, zero_div] at hlog
  apply hlog.congr'
  filter_upwards [hz.eventually (eventually_gt_atTop 0),
    ha.eventually (eventually_ne_nhds one_ne_zero),
    hb.eventually (eventually_ne_nhds one_ne_zero)] with i hzi hai hbi
  have hzne : z i ≠ 0 := norm_pos_iff.mp hzi
  have hfactor (q : Plane) : ‖z i-q‖ = ‖z i‖ * ‖1-q*(z i)⁻¹‖ := by
    rw [← norm_mul]
    congr 1
    field_simp
  unfold green
  rw [hfactor (star w), hfactor w,
    Real.log_mul (norm_ne_zero_iff.mpr hzne) (norm_ne_zero_iff.mpr hai),
    Real.log_mul (norm_ne_zero_iff.mpr hzne) (norm_ne_zero_iff.mpr hbi)]
  ring

end Torsion.HalfPlane

namespace Torsion.Spectral

/-- The physical Green kernel has zero marked trace along every actual
interior approach, without restricting the approach to a normal curve. -/
theorem physicalGreen_marked_boundary_tendsto {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) (v : Plane) :
    Tendsto (fun w => physicalGreen φ w v) (𝓝[cauchyImage φ] 0) (𝓝 0) :=
  HalfPlane.green_tendsto_zero_of_norm_tendsto
    (cauchyInverse_norm_tendsto_at_marked hφ hα0 hα1 hodd hzero hpos) (cauchyInverse φ v)

/-- Every point of the actual image frontier has the zero Dirichlet trace
of the concrete normalized weak Green function. -/
theorem physicalGreen_boundary_tendsto {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {v p : Plane} (hv : v ∈ cauchyImage φ) (hp : p ∈ frontier (cauchyImage φ)) :
    Tendsto (fun w => physicalGreen φ w v) (𝓝[cauchyImage φ] p) (𝓝 0) := by
  rw [frontier_cauchyImage_eq (hφ.continuous hα0) hodd hzero hpos] at hp
  rcases hp with ⟨t, rfl⟩ | hp
  · exact physicalGreen_finite_boundary_tendsto hφ hα0 hα1 hodd hzero hpos hv t
  · have hp0 : p = 0 := hp
    subst p
    exact physicalGreen_marked_boundary_tendsto hφ hα0 hα1 hodd hzero hpos v

end Torsion.Spectral

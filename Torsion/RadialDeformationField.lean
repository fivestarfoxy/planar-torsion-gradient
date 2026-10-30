module

public import Torsion.RadialDeformationCollar
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual smooth compact radial displacement fields

The field is the concrete polar formula `β(‖z‖) f(arg z) z/‖z‖`.
Its support lies in a compact polar image strictly inside the upper
half-plane. Smoothness across the argument branch and at the origin then
follows from actual vanishing on neighborhoods of those points.
-/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace Torsion.Shape

def radialDisplacement (β f : ℝ → ℝ) (z : Plane) : Plane :=
  (β ‖z‖ * f z.arg / ‖z‖) • z

@[simp] theorem radialDisplacement_zero (β f : ℝ → ℝ) : radialDisplacement β f 0 = 0 := by
  simp [radialDisplacement]

private def polarPoint (p : ℝ × ℝ) : Plane :=
  (p.1 : Plane) * Complex.exp ((p.2 : Plane) * Complex.I)

private theorem polarPoint_continuous : Continuous polarPoint := by
  unfold polarPoint
  fun_prop

private theorem polarPoint_im_pos {p : ℝ × ℝ}
    (hr : 0 < p.1) (hθ : p.2 ∈ Ioo 0 Real.pi) : 0 < (polarPoint p).im := by
  simpa [polarPoint, Complex.exp_mul_I, Complex.mul_im, Complex.sin_ofReal_re] using
    mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

private theorem radialDisplacement_tsupport_subset_polar {β f : ℝ → ℝ}
    {a b : ℝ} (hβ : tsupport β ⊆ Icc a b) (hfc : HasCompactSupport f) :
    tsupport (radialDisplacement β f) ⊆ polarPoint '' (Icc a b ×ˢ tsupport f) := by
  have hcompact : IsCompact (polarPoint '' (Icc a b ×ˢ tsupport f)) :=
    (isCompact_Icc.prod hfc).image polarPoint_continuous
  apply closure_minimal _ hcompact.isClosed
  intro z hz
  have hβz : β ‖z‖ ≠ 0 := by
    intro h
    exact hz (by simp [radialDisplacement, h])
  have hfz : f z.arg ≠ 0 := by
    intro h
    exact hz (by simp [radialDisplacement, h])
  refine ⟨(‖z‖, z.arg), ⟨hβ (subset_tsupport β hβz), subset_tsupport f hfz⟩, ?_⟩
  exact Complex.norm_mul_exp_arg_mul_I z

/-- The actual radial field has compact support strictly inside the upper
half-plane whenever its radial and angular cutoffs have the stated genuine
compact supports. -/
theorem radialDisplacement_compact_upper {β f : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hβ : tsupport β ⊆ Icc a b)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ Ioo 0 Real.pi) :
    HasCompactSupport (radialDisplacement β f) ∧
      tsupport (radialDisplacement β f) ⊆ upperHalfPlane := by
  have hsub := radialDisplacement_tsupport_subset_polar hβ hfc
  refine ⟨((isCompact_Icc.prod hfc).image polarPoint_continuous).of_isClosed_subset
    (isClosed_tsupport _) hsub, ?_⟩
  intro z hz
  obtain ⟨p, hp, rfl⟩ := hsub hz
  exact polarPoint_im_pos (ha.trans_le hp.1.1) (hfU hp.2)

theorem radialDisplacement_contDiff {β f : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hβ : ContDiff ℝ ∞ β) (hβsupp : tsupport β ⊆ Icc a b)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ Ioo 0 Real.pi) :
    ContDiff ℝ ∞ (radialDisplacement β f) := by
  have hsupport := (radialDisplacement_compact_upper ha hβsupp hfc hfU).2
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ Complex.slitPlane
  · have hnorm : ContDiffAt ℝ ∞ (norm : Plane → ℝ) z :=
      contDiffAt_norm ℝ (Complex.slitPlane_ne_zero hz)
    have harg : ContDiffAt ℝ ∞ Complex.arg z := by
      have hlog : ContDiffAt ℝ ∞ Complex.log z := (Complex.contDiffAt_log hz).restrict_scalars ℝ
      convert Complex.imCLM.contDiff.contDiffAt.comp z hlog using 1
      funext w
      exact (Complex.log_im w).symm
    exact (((hβ.contDiffAt.comp z hnorm).mul (hf.contDiffAt.comp z harg)).div hnorm
      (norm_ne_zero_iff.mpr (Complex.slitPlane_ne_zero hz))).smul contDiffAt_id
  · have hn : z ∉ tsupport (radialDisplacement β f) := by
      intro h
      apply hz
      have him : 0 < z.im := hsupport h
      exact Or.inr him.ne'
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)

/-- The field vanishes on an actual neighborhood of every real-axis point,
including the marked origin and both flat/free junctions. -/
theorem radialDisplacement_eventually_zero_at_real {β f : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hβ : tsupport β ⊆ Icc a b)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ Ioo 0 Real.pi) (x : ℝ) :
    radialDisplacement β f =ᶠ[𝓝 (x : Plane)] 0 := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  intro hx
  have h := (radialDisplacement_compact_upper ha hβ hfc hfU).2 hx
  simpa [upperHalfPlane] using h

/-- On each positive upper ray the actual field is the prescribed scalar
displacement in the radial unit direction. -/
theorem radialDisplacement_polar {β f : ℝ → ℝ} {r θ : ℝ}
    (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi) :
    radialDisplacement β f ((r : Plane) * Complex.exp ((θ : Plane) * Complex.I)) =
      (β r * f θ : ℝ) • Complex.exp ((θ : Plane) * Complex.I) := by
  have hnorm : ‖(r : Plane) * Complex.exp ((θ : Plane) * Complex.I)‖ = r := by
    simp [norm_mul, Complex.norm_exp_ofReal_mul_I, abs_of_pos hr]
  have harg : ((r : Plane) * Complex.exp ((θ : Plane) * Complex.I)).arg = θ := by
    rw [Complex.exp_mul_I]
    exact Complex.arg_mul_cos_add_sin_mul_I hr
      ⟨(neg_lt_zero.mpr Real.pi_pos).trans hθ.1, hθ.2.le⟩
  rw [radialDisplacement, hnorm, harg]
  change ((β r * f θ / r : ℝ) : Plane) *
    ((r : Plane) * Complex.exp ((θ : Plane) * Complex.I)) =
      ((β r * f θ : ℝ) : Plane) * Complex.exp ((θ : Plane) * Complex.I)
  rw [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hr.ne']

end Torsion.Shape

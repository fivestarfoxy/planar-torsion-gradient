module

public import Torsion.WeakHarmonicRegularity
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Explicit normalized radial smoothing kernels

The ordinary bump API may choose an arbitrary smooth bump base. Here the
inner-product-space base is used explicitly, so radial symmetry is proved.
-/
noncomputable section
open Set Filter MeasureTheory Function
open scoped Topology ENNReal ContDiff

namespace Torsion.WeakHarmonicRegularity

/-- An explicitly radial smooth bump with outer radius `r`. -/
def radialKernelRaw (r : ℝ) (z : Plane) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace Plane).toFun 2 ((2 / r) • z)

theorem radialKernelRaw_contDiff (r : ℝ) : ContDiff ℝ ∞ (radialKernelRaw r) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have hbase : ContDiffAt ℝ ∞
      (uncurry (ContDiffBumpBase.ofInnerProductSpace Plane).toFun) (2, (2 / r) • z) :=
    (ContDiffBumpBase.ofInnerProductSpace Plane).smooth.contDiffAt
      (prod_mem_nhds (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2)) univ_mem)
  have hmap : ContDiffAt ℝ ∞ (fun w : Plane => ((2 : ℝ), (2 / r) • w)) z :=
    (contDiff_const.prodMk (contDiff_const.smul contDiff_id)).contDiffAt
  have hcomp := hbase.comp z hmap
  exact hcomp

theorem radialKernelRaw_radial (r : ℝ) {z w : Plane} (hzw : ‖z‖ = ‖w‖) :
    radialKernelRaw r z = radialKernelRaw r w := by
  simp only [radialKernelRaw, ContDiffBumpBase.ofInnerProductSpace,
    norm_smul, Real.norm_eq_abs, hzw]

theorem radialKernelRaw_nonneg (r : ℝ) (z : Plane) : 0 ≤ radialKernelRaw r z :=
  ((ContDiffBumpBase.ofInnerProductSpace Plane).mem_Icc _ _).1

theorem radialKernelRaw_support {r : ℝ} (hr : 0 < r) :
    Function.support (radialKernelRaw r) = Metric.ball (0 : Plane) r := by
  change Function.support ((ContDiffBumpBase.ofInnerProductSpace Plane).toFun 2 ∘
    fun z : Plane => (2 / r) • z) = _
  rw [support_comp_eq_preimage,
    (ContDiffBumpBase.ofInnerProductSpace Plane).support 2 (by norm_num)]
  ext z
  simp only [mem_preimage, Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hr)]
  rw [div_mul_eq_mul_div, div_lt_iff₀ hr]
  constructor <;> intro h <;> linarith

theorem radialKernelRaw_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (radialKernelRaw r) = Metric.closedBall (0 : Plane) r := by
  rw [tsupport, radialKernelRaw_support hr, closure_ball _ hr.ne']

theorem radialKernelRaw_hasCompactSupport {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (radialKernelRaw r) := by
  rw [HasCompactSupport, radialKernelRaw_tsupport hr]
  exact isCompact_closedBall _ _

theorem radialKernelRaw_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (radialKernelRaw r) :=
  (radialKernelRaw_contDiff r).continuous.integrable_of_hasCompactSupport
    (radialKernelRaw_hasCompactSupport hr)

theorem radialKernelRaw_integral_pos {r : ℝ} (hr : 0 < r) :
    0 < ∫ z : Plane, radialKernelRaw r z := by
  apply (integral_pos_iff_support_of_nonneg (radialKernelRaw_nonneg r)
    (radialKernelRaw_integrable hr)).mpr
  rw [radialKernelRaw_support hr]
  exact Metric.measure_ball_pos volume 0 hr

/-- The explicitly radial kernel normalized against actual planar volume. -/
def radialKernel (r : ℝ) (z : Plane) : ℝ :=
  radialKernelRaw r z / ∫ w : Plane, radialKernelRaw r w

theorem radialKernel_contDiff (r : ℝ) : ContDiff ℝ ∞ (radialKernel r) :=
  (radialKernelRaw_contDiff r).div_const _

theorem radialKernel_nonneg {r : ℝ} (hr : 0 < r) (z : Plane) :
    0 ≤ radialKernel r z :=
  div_nonneg (radialKernelRaw_nonneg r z) (radialKernelRaw_integral_pos hr).le

theorem radialKernel_radial (r : ℝ) {z w : Plane} (hzw : ‖z‖ = ‖w‖) :
    radialKernel r z = radialKernel r w := by
  unfold radialKernel
  rw [radialKernelRaw_radial r hzw]

theorem radialKernel_support {r : ℝ} (hr : 0 < r) :
    Function.support (radialKernel r) = Metric.ball (0 : Plane) r := by
  unfold radialKernel
  rw [← radialKernelRaw_support hr]
  ext z
  simp only [Function.mem_support, div_ne_zero_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, (radialKernelRaw_integral_pos hr).ne'⟩⟩

theorem radialKernel_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (radialKernel r) = Metric.closedBall (0 : Plane) r := by
  rw [tsupport, radialKernel_support hr, closure_ball _ hr.ne']

theorem radialKernel_hasCompactSupport {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (radialKernel r) := by
  rw [HasCompactSupport, radialKernel_tsupport hr]
  exact isCompact_closedBall _ _

theorem radialKernel_integrable {r : ℝ} (hr : 0 < r) : Integrable (radialKernel r) :=
  (radialKernelRaw_integrable hr).div_const _

theorem radialKernel_integral {r : ℝ} (hr : 0 < r) :
    (∫ z : Plane, radialKernel r z) = 1 := by
  simp only [radialKernel, integral_div]
  exact div_self (radialKernelRaw_integral_pos hr).ne'

end Torsion.WeakHarmonicRegularity

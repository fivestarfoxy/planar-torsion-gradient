module

public import Torsion.WeakHarmonicWeyl.RadialKernel
public import Torsion.RestrictedSpectralOddKernelMinimum

@[expose] public section

/-! # A common nonnegative probe for volume and boundary blow-ups -/

noncomputable section
open Set MeasureTheory Metric
open scoped Topology
namespace Torsion.HermiteHadamard
open WeakHarmonicRegularity

/-- The restriction of the fixed radius-one physical probe to the real axis. -/
def boundaryBumpProfile (t : ℝ) : ℝ := radialKernelRaw 1 (t : Plane)

theorem boundaryBumpProfile_continuous : Continuous boundaryBumpProfile :=
  (radialKernelRaw_contDiff 1).continuous.comp Complex.continuous_ofReal

theorem boundaryBumpProfile_zero {t : ℝ} (ht : 1 ≤ |t|) : boundaryBumpProfile t = 0 := by
  change radialKernelRaw 1 (t : Plane) = 0
  apply Function.notMem_support.mp
  rw [radialKernelRaw_support (by norm_num : (0:ℝ)<1)]
  simpa [Real.norm_eq_abs] using (not_lt.mpr ht)

theorem boundaryBumpProfile_ramp (z : Plane) :
    radialKernelRaw 1 z = boundaryBumpProfile ‖z‖ := by
  apply radialKernelRaw_radial
  simp

theorem boundaryBumpProfile_line {v : Plane} (hv : ‖v‖ = 1) :
    (∫ t : ℝ, radialKernelRaw 1 (t • v)) = 2 * ∫ t in Ioi (0 : ℝ), boundaryBumpProfile t := by
  have he (t : ℝ) : radialKernelRaw 1 (t • v) = boundaryBumpProfile t := by
    apply radialKernelRaw_radial
    simp [hv, Real.norm_eq_abs]
  simp_rw [he]
  have hK : HasCompactSupport boundaryBumpProfile := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 1)
    intro x hx
    exact boundaryBumpProfile_zero (by simpa [Real.norm_eq_abs] using
      (le_of_lt (not_le.mp (show ¬ dist x 0 ≤ 1 from hx))))
  rw [Spectral.integral_eq_positive_reflection (boundaryBumpProfile_continuous.integrable_of_hasCompactSupport hK),
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  have heven : boundaryBumpProfile (-x) = boundaryBumpProfile x := by
    apply radialKernelRaw_radial
    simp
  dsimp only
  rw [heven, two_mul]

theorem boundaryBumpProfile_line_pos : 0 < 2 * ∫ t in Ioi (0 : ℝ), boundaryBumpProfile t := by
  rw [← boundaryBumpProfile_line (v := 1) (by simp)]
  let F := fun t : ℝ => radialKernelRaw 1 (t • (1 : Plane))
  have hc : Continuous F := (radialKernelRaw_contDiff 1).continuous.comp (continuous_id.smul continuous_const)
  have hK : HasCompactSupport F := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 1)
    intro x hx
    change radialKernelRaw 1 (x • (1 : Plane)) = 0
    apply Function.notMem_support.mp
    rw [radialKernelRaw_support (by norm_num : (0:ℝ)<1)]
    exact fun hz => hx (by simpa [norm_smul, Real.norm_eq_abs] using le_of_lt (show dist (x • (1:Plane)) 0 < 1 from hz))
  apply integral_pos_of_integrable_nonneg_nonzero hc (hc.integrable_of_hasCompactSupport hK)
    (fun t => radialKernelRaw_nonneg _ _) (x := 0)
  change (0:ℝ) • (1:Plane) ∈ Function.support (radialKernelRaw 1)
  rw [radialKernelRaw_support (by norm_num : (0:ℝ)<1)]
  simp

end Torsion.HermiteHadamard

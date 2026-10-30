import Torsion.ContinuousProfiles
import Torsion.ConvexOuterApproximation
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Positive radial representatives of centered convex domains

The Minkowski gauge gives a positive continuous profile for the upper-half
portion of every bounded open convex neighborhood of the origin. In
particular, thickening a convex competitor based at a supporting boundary
point produces genuine positive radial outer domains without requiring a
degenerate endpoint profile or boundary regularity.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Pointwise Topology
namespace Torsion

/-- The actual unit vector at polar angle `θ`. -/
def gaugeDirection (θ : ℝ) : Plane := Complex.exp ((θ : ℂ) * Complex.I)

@[simp] theorem gaugeDirection_ne_zero (θ : ℝ) : gaugeDirection θ ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem norm_gaugeDirection (θ : ℝ) : ‖gaugeDirection θ‖ = 1 := by
  simp [gaugeDirection, Complex.norm_exp_ofReal_mul_I]

@[fun_prop] theorem continuous_gaugeDirection : Continuous gaugeDirection := by
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

/-- The concrete positive radius of a centered convex domain. -/
def convexGaugeRadius (D : ConvexDomain) (θ : ℝ) : ℝ :=
  (gauge D.carrier (gaugeDirection θ))⁻¹

theorem convexGaugeRadius_pos (D : ConvexDomain) (hzero : (0 : Plane) ∈ D.carrier)
    (θ : ℝ) : 0 < convexGaugeRadius D θ := by
  apply inv_pos.mpr
  exact (gauge_pos (absorbent_nhds_zero (D.isOpen.mem_nhds hzero))
    (NormedSpace.isVonNBounded_of_isBounded ℝ D.bounded)).mpr (gaugeDirection_ne_zero θ)

theorem continuous_convexGaugeRadius (D : ConvexDomain) (hzero : (0 : Plane) ∈ D.carrier) :
    Continuous (convexGaugeRadius D) := by
  apply Continuous.inv₀
  · exact (continuous_gauge D.convex (D.isOpen.mem_nhds hzero)).comp continuous_gaugeDirection
  · intro θ
    exact ne_of_gt (inv_pos.mp (convexGaugeRadius_pos D hzero θ))

/-- The gauge radius as a profile on the full closed angular interval. -/
def convexGaugeProfile (D : ConvexDomain) (hzero : (0 : Plane) ∈ D.carrier) :
    ContinuousProfiles.Profile :=
  ⟨fun θ => convexGaugeRadius D θ,
    (continuous_convexGaugeRadius D hzero).comp continuous_subtype_val⟩

@[simp] theorem convexGaugeProfile_apply (D : ConvexDomain) (hzero : (0 : Plane) ∈ D.carrier)
    (θ : ContinuousProfiles.Angle) : convexGaugeProfile D hzero θ = convexGaugeRadius D θ := rfl

theorem convexGaugeProfile_pos (D : ConvexDomain) (hzero : (0 : Plane) ∈ D.carrier)
    (θ : ContinuousProfiles.Angle) : 0 < convexGaugeProfile D hzero θ :=
  convexGaugeRadius_pos D hzero θ

/-- Exact physical membership in the upper-half gauge domain. -/
theorem radialDomain_convexGaugeProfile (D : ConvexDomain) (hzero : (0 : Plane) ∈ D.carrier) :
    radialDomain (ContinuousProfiles.extend (convexGaugeProfile D hzero)) =
      D.carrier ∩ upperHalfPlane := by
  ext z
  rw [RadialGeometry.mem_radialDomain_iff]
  constructor
  · rintro ⟨hz, hr⟩
    have harg : z.arg ∈ Icc (0 : ℝ) Real.pi :=
      ⟨Complex.arg_nonneg_iff.mpr hz.le, Complex.arg_le_pi _⟩
    have hext : ContinuousProfiles.extend (convexGaugeProfile D hzero) z.arg =
        convexGaugeRadius D z.arg :=
      ContinuousProfiles.extend_coe _ ⟨z.arg, harg⟩
    rw [hext, convexGaugeRadius] at hr
    have hg : 0 < gauge D.carrier (gaugeDirection z.arg) :=
      inv_pos.mp (convexGaugeRadius_pos D hzero z.arg)
    have hpolar : ‖z‖ • gaugeDirection z.arg = z := by
      simpa only [gaugeDirection, Complex.real_smul] using Complex.norm_mul_exp_arg_mul_I z
    have hgz : gauge D.carrier z = ‖z‖ * gauge D.carrier (gaugeDirection z.arg) := by
      calc
        gauge D.carrier z = gauge D.carrier (‖z‖ • gaugeDirection z.arg) :=
          congrArg (gauge D.carrier) hpolar.symm
        _ = _ := by
          simpa only [smul_eq_mul] using
            gauge_smul_of_nonneg (s := D.carrier) (norm_nonneg z) (gaugeDirection z.arg)
    refine ⟨?_, hz⟩
    rw [← gauge_lt_one_eq_self_of_isOpen D.convex hzero D.isOpen]
    change gauge D.carrier z < 1
    rw [hgz]
    rw [inv_eq_one_div, lt_div_iff₀ hg] at hr
    exact hr
  · rintro ⟨hzD, hz⟩
    have harg : z.arg ∈ Icc (0 : ℝ) Real.pi :=
      ⟨Complex.arg_nonneg_iff.mpr hz.le, Complex.arg_le_pi _⟩
    have hext : ContinuousProfiles.extend (convexGaugeProfile D hzero) z.arg =
        convexGaugeRadius D z.arg :=
      ContinuousProfiles.extend_coe _ ⟨z.arg, harg⟩
    refine ⟨hz, ?_⟩
    rw [hext, convexGaugeRadius]
    have hg : 0 < gauge D.carrier (gaugeDirection z.arg) :=
      inv_pos.mp (convexGaugeRadius_pos D hzero z.arg)
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ hg).mpr
    have hpolar : ‖z‖ • gaugeDirection z.arg = z := by
      simpa only [gaugeDirection, Complex.real_smul] using Complex.norm_mul_exp_arg_mul_I z
    have hgz : gauge D.carrier z = ‖z‖ * gauge D.carrier (gaugeDirection z.arg) := by
      calc
        gauge D.carrier z = gauge D.carrier (‖z‖ • gaugeDirection z.arg) :=
          congrArg (gauge D.carrier) hpolar.symm
        _ = _ := by
          simpa only [smul_eq_mul] using
            gauge_smul_of_nonneg (s := D.carrier) (norm_nonneg z) (gaugeDirection z.arg)
    rw [← hgz]
    exact gauge_lt_one_of_mem_of_isOpen D.isOpen hzD

end Torsion

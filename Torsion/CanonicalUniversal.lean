import Torsion.UniformSupportedCollar
import Torsion.NormalFrameFlatPatch
import Torsion.ConvexSupportingPoint
import Torsion.ConvexTorsionContinuity

/-!
# The universal sharp bound over the original convex admissible class

At each point of a fixed convex domain an actual nearest supporting point
provides normal coordinates. One fixed inball and one diameter bound supply
uniform parameters for the proved flat-hull comparison. Arbitrarily small
losses in the resulting collar estimate disappear by weak translation
comparison. All value and gradient representatives are constructed.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion
open Spectral

/-- A uniform approximate sharp boundary-distance collar estimate for every
actual continuous representative of convex-domain weak torsion. -/
theorem IsWeakTorsion.second_boundary_collar
    {D : ConvexDomain} {u U : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D.carrier u g) (hc : Continuous U)
    (hrep : u =ᵐ[volume.restrict D.carrier] U) (hzero : ∀ x ∉ D.carrier, U x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ D.carrier, infDist x D.carrierᶜ < δ →
      U x ≤ (spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt D.area + ε) *
        infDist x D.carrierᶜ := by
  have hweak := hu.of_zero_extension_representative D.isOpen.measurableSet hrep hzero
  obtain ⟨a, h, M, hh, hM, ha, hball, hsupport⟩ := D.exists_uniform_support_inball
  obtain ⟨R, hR, hRD⟩ := D.bounded.closure.subset_ball_lt 0 (0 : Plane)
  let b : ℝ := 2*R+1
  have hb : 0 ≤ b := by dsimp [b]; linarith
  obtain ⟨δ, hδ, hnormal⟩ := exists_uniform_second_supported_normal_bound
    (A := D.area) (h := h) (M := M) (b := b) ENNReal.toReal_nonneg hh hM hb hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxδ
  obtain ⟨p, hp, hd, hnorm, hn, hs⟩ := D.exists_nearest_supported_frontier hx
  let d : ℝ := infDist x D.carrierᶜ
  let n : Plane := d⁻¹ • (x-p)
  let e := normalFrame n hn
  let E := D.inNormalFrame p n hn
  let a' : Plane := e.symm (a-p)
  obtain ⟨hheight, hdisplacement⟩ := hsupport p hp n hn hs
  obtain ⟨ha', hball', hheight', hnorm'⟩ :=
    D.inNormalFrame_inball_bounds p n a hn hh hball hheight hdisplacement
  have hhalf : E.carrier ⊆ upperHalfPlane := D.inNormalFrame_subset_upper p n hn hs
  have hzeroE : (0 : Plane) ∈ closure E.carrier :=
    D.zero_mem_closure_inNormalFrame p n hn (frontier_subset_closure hp)
  have hupper : ∀ z ∈ E.carrier, z.im ≤ b := by
    intro z hz
    have hzD := (D.mem_inNormalFrame p n z hn).mp hz
    have hzR : ‖e z+p‖ < R := by
      simpa only [mem_ball, dist_zero_right] using hRD (subset_closure hzD)
    have hpR : ‖p‖ < R := by
      simpa only [mem_ball, dist_zero_right] using hRD (frontier_subset_closure hp)
    have hzbound : ‖z‖ < 2*R := by
      calc
        ‖z‖ = ‖e z‖ := (e.norm_map z).symm
        _ = ‖(e z+p)-p‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖e z+p‖ + ‖p‖ := norm_sub_le _ _
        _ < 2*R := by linarith
    exact (Complex.im_le_norm z).trans (hzbound.le.trans (by dsimp [b]; linarith))
  have hpoint : e ((d : Plane)*Complex.I) + p = x := by
    rw [← Complex.real_smul, map_smul, normalFrame_I]
    change d • (d⁻¹ • (x-p)) + p = x
    rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul, sub_add_cancel]
  have hline : (d : Plane)*Complex.I ∈ E.carrier := by
    apply (D.mem_inNormalFrame p n _ hn).mpr
    change e ((d : Plane)*Complex.I) + p ∈ D.carrier
    rwa [hpoint]
  have hcE : ContinuousOn (fun z => U (e z+p)) E.carrier :=
    (hc.comp (e.continuous.add continuous_const)).continuousOn
  have hbound := hnormal (D.inNormalFrame_area p n hn) hhalf hzeroE ha' hball' hheight' hnorm'
    hupper (hweak.inNormalFrame p n hn) hcE EventuallyEq.rfl d hd hxδ hline
  change U (e ((d : Plane)*Complex.I)+p) ≤ _ at hbound
  rw [hpoint] at hbound
  exact hbound

/-- The sharp bound is proved for every original convex competitor, for
the actual weak-gradient essential supremum and every Dirichlet solution
choice. No stationarity, boundary regularity or comparison premise remains. -/
theorem DirichletTheory.G_le_second_spectral_bound (T : DirichletTheory) (D : ConvexDomain) :
    T.G D ≤ ENNReal.ofReal
      (spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt D.area) := by
  have hu := (T.solution D).weakEquation
  obtain ⟨U, hc, hs, hz, hp, hrep, hg⟩ := hu.exists_continuous_smooth_representative
  let L : ℝ≥0 := ⟨spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt D.area,
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)⟩
  have hb := hu.gradient_bound_of_boundary_collar_approx D.isOpen D.bounded hc hs hg hrep hz hp
    (L := L) (fun ε hε => hu.second_boundary_collar hc hrep hz hε)
  change eLpNorm (T.solution D).weakGradient ∞ (volume.restrict D.carrier) ≤
    ENNReal.ofReal (L : ℝ)
  rw [ENNReal.ofReal_coe_nnreal]
  exact hb

/-- The exact previously open `ReferenceCertificate.universal` inequality,
now proved on the full original admissible class. -/
theorem second_universal : ∀ D : ConvexDomain, torsionTheory.G D ≤ ENNReal.ofReal
    (2 * secondMoments.stationarity * Real.sqrt secondMoments.area * Real.sqrt D.area) := by
  intro D
  rw [secondMoments.calibration_constant_eq]
  exact torsionTheory.G_le_second_spectral_bound D

end Torsion

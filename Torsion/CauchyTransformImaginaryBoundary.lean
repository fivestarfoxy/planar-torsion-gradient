import Torsion.CauchyTransformPoisson
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Jointly continuous imaginary Cauchy boundary extension

Changing variables in the actual Poisson integral produces a fixed
integrable kernel.  Dominated convergence then proves joint continuity as
the real and imaginary coordinates vary together, including at the boundary.
This strengthens the earlier vertical imaginary trace theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Torsion.Spectral

/-- The fixed-kernel Poisson extension, defined on the whole plane.  For
positive height it is the usual Poisson integral; at zero height it is `f`. -/
def poissonExtension (f : ℝ → ℝ) (z : ℂ) : ℝ :=
  ∫ t : ℝ, poissonDensity t * f (z.re + z.im * t)

theorem poissonDensity_continuous : Continuous poissonDensity := by
  unfold poissonDensity
  apply continuous_const.mul
  apply Continuous.inv₀ (continuous_const.add (continuous_id.pow 2))
  intro t
  positivity

theorem poissonDensity_integrable : Integrable poissonDensity :=
  integrable_inv_one_add_sq.const_mul _

/-- Continuous densities with the prescribed zero exterior values have
genuine compact support in the integration interval. -/
theorem cauchyDensity_hasCompactSupport {f : ℝ → ℝ}
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) : HasCompactSupport f := by
  apply HasCompactSupport.intro (K := Icc (-1 : ℝ) 1) isCompact_Icc
  intro s hs
  have hnot : ¬ |s| < 1 := fun h => hs (abs_le.1 h.le)
  exact hzero s (le_of_not_gt hnot)

/-- The fixed-kernel extension is jointly continuous.  Its single DCT
majorant is the Poisson density times a proved global bound on the compactly
supported data. -/
theorem poissonExtension_continuous {f : ℝ → ℝ}
    (hf : Continuous f) (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) :
    Continuous (poissonExtension f) := by
  obtain ⟨B, hB⟩ := (cauchyDensity_hasCompactSupport hzero).exists_bound_of_continuous hf
  apply continuous_of_dominated (bound := fun t => poissonDensity t * B)
  · intro z
    exact (poissonDensity_continuous.mul
      (hf.comp (continuous_const.add (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · intro z
    exact ae_of_all _ fun t => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (poissonDensity_nonneg t)]
      exact mul_le_mul_of_nonneg_left (hB _) (poissonDensity_nonneg t)
  · exact poissonDensity_integrable.mul_const B
  · exact ae_of_all _ fun t =>
      continuous_const.mul (hf.comp
        (Complex.continuous_re.add (Complex.continuous_im.mul continuous_const)))

/-- At a real boundary point the fixed-kernel formula is exactly the
original density, because the Poisson density has total integral one. -/
theorem poissonExtension_ofReal (f : ℝ → ℝ) (x : ℝ) :
    poissonExtension f (x : ℂ) = f x := by
  simp only [poissonExtension, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, integral_mul_const, integral_poissonDensity, one_mul]

/-- The imaginary part of the actual Cauchy transform is the fixed-kernel
Poisson extension at every interior point.  The proof performs the affine
change of variables rather than presuming a boundary theorem. -/
theorem realCauchy_im_eq_poissonExtension {f : ℝ → ℝ}
    (hf : Continuous f) (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (realCauchy f z).im = poissonExtension f z := by
  rw [realCauchy_im_eq_poisson hf hz]
  let q : ℝ → ℝ := fun s =>
    (Real.pi⁻¹ * z.im / ((z.re - s) ^ 2 + z.im ^ 2)) * f s
  have hglobal : (∫ s in Icc (-1 : ℝ) 1, q s) = ∫ s : ℝ, q s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    have hnot : ¬ |s| < 1 := fun h => hs (abs_le.1 h.le)
    simp [q, hzero s (le_of_not_gt hnot)]
  change (∫ s in Icc (-1 : ℝ) 1, q s) = _
  rw [hglobal]
  have hy : 0 < z.im := hz
  have hpoint (t : ℝ) : q (z.re + z.im * t) =
      z.im⁻¹ * (poissonDensity t * f (z.re + z.im * t)) := by
    dsimp [q, poissonDensity]
    have hd : (z.re - (z.re + z.im * t)) ^ 2 + z.im ^ 2 ≠ 0 :=
      ne_of_gt (by positivity)
    have hd' : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hy.ne', hd, hd', Real.pi_ne_zero]
    ring
  have hchange := Measure.integral_comp_mul_left (fun s => q (z.re + s)) z.im
  rw [integral_add_left_eq_self] at hchange
  simp_rw [hpoint] at hchange
  rw [integral_const_mul, abs_of_pos (inv_pos.mpr hy), smul_eq_mul] at hchange
  exact (mul_left_cancel₀ (inv_ne_zero hy.ne') hchange).symm

/-- Joint upper-half-plane boundary convergence allows arbitrary approach
directions, unlike a vertical-only trace statement. -/
theorem realCauchy_im_boundary_tendsto {f : ℝ → ℝ}
    (hf : Continuous f) (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) (x : ℝ) :
    Tendsto (fun z => (realCauchy f z).im) (𝓝[upperHalfPlane] (x : ℂ)) (𝓝 (f x)) := by
  have h := (poissonExtension_continuous hf hzero).continuousAt.continuousWithinAt
    (s := upperHalfPlane) (x := (x : ℂ))
  change Tendsto (poissonExtension f) (𝓝[upperHalfPlane] (x : ℂ))
    (𝓝 (poissonExtension f (x : ℂ))) at h
  rw [poissonExtension_ofReal] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (realCauchy_im_eq_poissonExtension hf hzero hz).symm

end Torsion.Spectral

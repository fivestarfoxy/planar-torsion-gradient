module

public import Torsion.WeakReflection.Tests
public import Torsion.WeakHarmonicWeyl
public import Torsion.SobolevSupport

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Odd reflection across a flat zero boundary

An actual H¹₀ pair on the upper half-plane, weakly harmonic on a half-ball,
has a genuinely weakly harmonic odd extension on the whole ball.  The test
crossing the diameter is admitted using the proved half-plane trace argument,
not supplied as an extra hypothesis.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

private theorem gradient_sub_of_differentiable {f h : Plane → ℝ}
    (hf : Differentiable ℝ f) (hh : Differentiable ℝ h) (x : Plane) :
    gradient (fun z => f z - h z) x = gradient f x - gradient h x := by
  simp only [gradient, fderiv_sub (hf x) (hh x), map_sub]

private theorem reflected_gradient_test_integral {g : Plane → Plane}
    (ψ : Plane → ℝ) :
    (∫ z, inner (𝕜 := ℝ) (reflectedGradient g z) (gradient ψ z)) =
      ∫ z, inner (𝕜 := ℝ) (g z) (reflectedGradient (gradient ψ) z) := by
  calc
    _ = ∫ z, inner (𝕜 := ℝ) (g (star z)) (star (gradient ψ z)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => real_inner_conjugate_left _ _
    _ = _ := by
      simpa only [reflectedGradient, star_star] using
        integral_comp_conjugation
          (fun z => inner (𝕜 := ℝ) (g z) (star (gradient ψ (star z))))

/-- Actual odd reflection of a weakly harmonic H¹₀ half-plane pair across
the flat diameter. Its value and supplied gradient are concrete functions. -/
theorem IsWeakHarmonicOn.odd_reflection {u : Plane → ℝ} {g : Plane → Plane}
    {r : ℝ} (hu : MemH10 upperHalfPlane u g)
    (hw : IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 r) u g) :
    IsWeakHarmonicOn (Metric.ball 0 r)
      (fun z => u z - reflectedValue u z)
      (fun z => g z - reflectedGradient g z) := by
  have hrefl := hu.reflectedValue
  refine ⟨((hu.mono (subset_univ _)).sub
    (hrefl.mono (subset_univ _))).distributionalGradient, ?_⟩
  intro ψ hψ
  have hψr : IsTest (Metric.ball 0 r) (reflectedValue ψ) := by
    convert hψ.reflectedValue using 1
    ext z
    simp [Metric.mem_ball, dist_zero_right]
  let ρ : Plane → ℝ := fun z => ψ z - reflectedValue ψ z
  have hρ : IsTest (Metric.ball 0 r) ρ := hψ.sub hψr
  have hρodd : ∀ z, ρ (star z) = -ρ z := by
    intro z
    simp only [ρ, reflectedValue, star_star]
    ring
  have hmask := hρ.upperHalfPlane_indicator hρodd
  have hmaskLocal : MemH10 (upperHalfPlane ∩ Metric.ball 0 r)
      (upperHalfPlane.indicator ρ) (upperHalfPlane.indicator (gradient ρ)) := by
    apply hmask.localize_compact_inter Metric.isOpen_ball hρ.2.1 hρ.2.2
    exact ae_of_all _ fun z hz => by
      by_cases hzU : z ∈ upperHalfPlane
      · rw [indicator_of_mem hzU, image_eq_zero_of_nmem_tsupport hz]
      · exact indicator_of_not_mem hzU _
  have heq := hw.sobolev_test_equation hu.2.1 hmaskLocal
  have hgOff : ∀ᵐ z ∂volume, z ∉ upperHalfPlane → g z = 0 :=
    (ae_restrict_iff' (isOpen_lt continuous_const Complex.continuous_im).measurableSet.compl).mp
      hu.gradient_ae_zero_off
  have heq' : (∫ z, inner (𝕜 := ℝ) (g z) (gradient ρ z)) = 0 := by
    convert heq using 1
    apply integral_congr_ae
    filter_upwards [hgOff] with z hz
    by_cases hzU : z ∈ upperHalfPlane
    · rw [indicator_of_mem hzU]
    · simp [indicator_of_not_mem hzU, hz hzU]
  have hgrad (z : Plane) : gradient ρ z =
      gradient ψ z - reflectedGradient (gradient ψ) z := by
    rw [gradient_sub_of_differentiable (hψ.1.differentiable (by simp))
      (hψr.1.differentiable (by simp)),
      gradient_reflectedValue (hψ.1.differentiable (by simp) _)]
  have hi := integrable_real_inner_of_memLp_two hu.2.1 (hψ.memLp_gradient (p := 2))
  have hir := integrable_real_inner_of_memLp_two
    (memLp_reflectedGradient hu.2.1) (hψ.memLp_gradient (p := 2))
  have higr := integrable_real_inner_of_memLp_two hu.2.1
    (memLp_reflectedGradient (hψ.memLp_gradient (p := 2)))
  simp only [hgrad, inner_sub_right] at heq'
  rw [integral_sub hi higr] at heq'
  simp only [inner_sub_left]
  rw [integral_sub hi hir, reflected_gradient_test_integral]
  exact heq'

/-- The odd extension agrees with the original zero-extended value a.e. in
the upper half-plane. This allows a smooth reflected representative to be
used as the marked representative of the original solution. -/
theorem MemH10.odd_reflection_ae_upper {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 upperHalfPlane u g) :
    (fun z => u z - Torsion.reflectedValue u z) =ᵐ[volume.restrict upperHalfPlane] u := by
  have hU : MeasurableSet upperHalfPlane :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hOff : ∀ᵐ z ∂volume, z ∉ upperHalfPlane → u z = 0 :=
    (ae_restrict_iff' hU.compl).mp hu.value_ae_zero_off
  have hr := measurePreserving_conjugation.quasiMeasurePreserving.ae hOff
  apply (ae_restrict_iff' hU).mpr
  filter_upwards [hr] with z hz
  intro hzU
  have hzStar : star z ∉ upperHalfPlane := by
    change ¬ 0 < (star z).im
    have him : (star z).im = -z.im := Complex.conj_im z
    rw [him]
    exact not_lt_of_ge (neg_nonpos.mpr hzU.le)
  simp only [Torsion.reflectedValue, hz hzStar, sub_zero]

/-- The reflected weak gradient likewise agrees with the original weak
gradient a.e. in the original upper half-plane. -/
theorem MemH10.odd_reflection_gradient_ae_upper {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 upperHalfPlane u g) :
    (fun z => g z - reflectedGradient g z) =ᵐ[volume.restrict upperHalfPlane] g := by
  have hU : MeasurableSet upperHalfPlane :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hOff : ∀ᵐ z ∂volume, z ∉ upperHalfPlane → g z = 0 :=
    (ae_restrict_iff' hU.compl).mp hu.gradient_ae_zero_off
  have hr := measurePreserving_conjugation.quasiMeasurePreserving.ae hOff
  apply (ae_restrict_iff' hU).mpr
  filter_upwards [hr] with z hz
  intro hzU
  have hzStar : star z ∉ upperHalfPlane := by
    change ¬ 0 < (star z).im
    have him : (star z).im = -z.im := Complex.conj_im z
    rw [him]
    exact not_lt_of_ge (neg_nonpos.mpr hzU.le)
  simp only [reflectedGradient, hz hzStar, star_zero, sub_zero]

end Torsion

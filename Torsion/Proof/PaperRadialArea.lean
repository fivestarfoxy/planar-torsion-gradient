module

public import Torsion.PolarIntegrability
public import Torsion.Definitions
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! # Integrating over a planar frame using its physical polar radius -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Torsion

/-- Area integral on an open frame described by its radial sections.
The ray through the polar-coordinate cut and the two endpoints of a radial
interval have zero planar or one-dimensional measure respectively. -/
theorem integral_radial_frame {D : Set Plane} (c : Plane) (R : ℝ → ℝ)
    (hD : MeasurableSet D) {f : Plane → ℝ} (hf : IntegrableOn f D)
    (hR : ∀ θ ∈ Ioo (-Real.pi) Real.pi, 0 < R θ)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D ↔ r < R θ)) :
    (∫ z in D, f z) = ∫ θ in (-Real.pi)..Real.pi, ∫ r in (0:ℝ)..1,
      r * R θ ^ 2 * f (c + r • circleMap 0 (R θ) θ) := by
  classical
  let g : Plane → ℝ := fun z => D.indicator f (c + z)
  let F : ℝ × ℝ → ℝ := fun p => p.1 • g (Complex.polarCoord.symm p)
  have hgi : Integrable g := ((measurePreserving_add_left volume c).integrable_comp_emb
    (MeasurableEquiv.addLeft c).measurableEmbedding).mpr ((integrable_indicator_iff hD).mpr hf)
  have hi : IntegrableOn F (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := (integrable_iff_complex_polar g).mp hgi
  have hs : IntegrableOn (fun p : ℝ × ℝ => F p.swap)
      (Ioo (-Real.pi) Real.pi ×ˢ Ioi (0:ℝ)) ((volume : Measure ℝ).prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    apply Integrable.swap (f := F)
    rw [Measure.prod_restrict]
    exact hi
  have hstart : (∫ z in D, f z) = ∫ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, F p := by
    rw [← integral_indicator hD, ← integral_add_left_eq_self (D.indicator f) c,
      ← Complex.integral_comp_polarCoord_symm g]
    rfl
  rw [hstart, Measure.volume_eq_prod, ← setIntegral_prod_swap (μ := (volume : Measure ℝ)) (ν := volume)
    (Ioi (0:ℝ)) (Ioo (-Real.pi) Real.pi) F, setIntegral_prod _ hs,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ hθ
  let v := fun s : ℝ => s * f (c + circleMap 0 s θ)
  have hrestrict : (∫ r in Ioi (0:ℝ), F (r, θ)) = ∫ r in Ioo 0 (R θ), v r := by
    calc
      _ = ∫ r in Ioi (0:ℝ), (Iio (R θ)).indicator v r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hp : Complex.polarCoord.symm (r,θ) = circleMap 0 r θ := by simp [circleMap, Complex.exp_mul_I]
        change r * D.indicator f (c + Complex.polarCoord.symm (r,θ)) = _
        rw [hp]
        by_cases h : r < R θ
        · rw [indicator_of_mem ((hmem _ hθ _ hr).mpr h), indicator_of_mem (show r ∈ Iio (R θ) from h)]
        · rw [indicator_of_notMem (mt (hmem _ hθ _ hr).mp h),
            indicator_of_notMem (show r ∉ Iio (R θ) from h), mul_zero]
      _ = _ := by rw [setIntegral_indicator measurableSet_Iio]; rfl
  change (∫ r in Ioi (0:ℝ), F (r,θ)) = _
  rw [hrestrict, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (hR θ hθ).le]
  have hscale := intervalIntegral.smul_integral_comp_mul_right (a := (0:ℝ)) (b := 1) v (R θ)
  simp only [zero_mul, one_mul, smul_eq_mul] at hscale
  rw [← hscale, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  have he : circleMap 0 (r * R θ) θ = r • circleMap 0 (R θ) θ := by
    simp [circleMap, Complex.real_smul, mul_assoc]
  dsimp only [v]
  rw [he]
  ring

end Torsion

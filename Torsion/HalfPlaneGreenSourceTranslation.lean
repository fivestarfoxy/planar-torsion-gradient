module

public import Torsion.HalfPlaneGreenSource
public import Torsion.WeakReflection.Translation
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Translation of the concrete logarithmic source identity -/

noncomputable section
open Set MeasureTheory

namespace Torsion.HalfPlane

/-- The reciprocal-distance source gradient pairs integrably with every
actual compact smooth test, at every translated pole. -/
theorem fundamental_pairing_integrable_at {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) (w : Plane) :
    Integrable (fun z : Plane => inner (𝕜 := ℝ)
      (gradient (fundamental w) z) (gradient ψ z)) := by
  let η := Torsion.translatedValue (-w) ψ
  have hη := hψ.translatedValue (-w)
  have hI := (fundamental_pairing_integrable hη).comp_add_right (-w)
  apply hI.congr
  filter_upwards [(countable_singleton w).ae_not_mem volume] with z hz
  have hz : z ≠ w := by simpa using hz
  have hzw : z + -w ≠ 0 := by simpa using sub_ne_zero.mpr hz
  rw [(fundamental_hasGradientAt hzw).gradient, (fundamental_hasGradientAt hz).gradient]
  have hgrad : gradient η (z + -w) = gradient ψ z := by
    simpa [translatedValue, sub_neg_eq_add, add_assoc] using
      (gradient_translatedValue
        (hψ.1.differentiable (by simp) ((z + -w)-(-w))))
  rw [hgrad]
  simp [sub_eq_add_neg]

/-- The exact mass-one weak source identity holds at every physical pole. -/
theorem fundamental_weak_source_at {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) (w : Plane) :
    (∫ z : Plane, inner (𝕜 := ℝ) (gradient (fundamental w) z) (gradient ψ z)) = ψ w := by
  let η := Torsion.translatedValue (-w) ψ
  have hη := hψ.translatedValue (-w)
  have hpair :
      (∫ z : Plane, inner (𝕜 := ℝ) (gradient (fundamental w) (z+w)) (gradient ψ (z+w))) =
      ∫ z : Plane, inner (𝕜 := ℝ) (gradient (fundamental 0) z) (gradient η z) := by
    apply integral_congr_ae
    filter_upwards [(countable_singleton (0 : Plane)).ae_not_mem volume] with z hz
    have hz : z ≠ 0 := by simpa using hz
    have hzw : z+w ≠ w := by simpa using hz
    rw [(fundamental_hasGradientAt hzw).gradient,
      (fundamental_hasGradientAt hz).gradient]
    have hgrad : gradient η z = gradient ψ (z+w) := by
      simpa only [translatedValue, sub_neg_eq_add] using (gradient_translatedValue
        (hψ.1.differentiable (by simp) (z-(-w))))
    rw [hgrad]
    simp
  rw [← integral_add_right_eq_self
    (fun z : Plane => inner (𝕜 := ℝ) (gradient (fundamental w) z) (gradient ψ z)) w,
    hpair, fundamental_weak_source hη]
  simp [η, translatedValue]

private theorem green_gradient_sub_fundamental {z w : Plane}
    (hp : z ≠ w) (hr : z ≠ star w) :
    gradient (fun u => green u w) z =
      gradient (fundamental w) z - gradient (fundamental (star w)) z := by
  rw [(green_hasGradientAt hr hp).gradient, (fundamental_hasGradientAt hp).gradient,
    (fundamental_hasGradientAt hr).gradient]
  simp [smul_sub, neg_smul, sub_eq_add_neg, add_comm]

/-- The Green-gradient/test pairing is genuinely integrable; this permits
subtraction of the source and its reflected source in the weak equation. -/
theorem green_pairing_integrable {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) (w : Plane) :
    Integrable (fun z : Plane => inner (𝕜 := ℝ)
      (gradient (fun u => green u w) z) (gradient ψ z)) := by
  apply ((fundamental_pairing_integrable_at hψ w).sub
    (fundamental_pairing_integrable_at hψ (star w))).congr
  filter_upwards [(countable_singleton w).ae_not_mem volume,
    (countable_singleton (star w)).ae_not_mem volume] with z hp hr
  have hp : z ≠ w := by simpa using hp
  have hr : z ≠ star w := by simpa using hr
  rw [green_gradient_sub_fundamental hp hr, inner_sub_left]
  rfl

/-- On the whole plane the method-of-images formula has the exact weak
source `δ_w - δ_conj(w)`, with both masses fixed, rather than a free factor. -/
theorem green_weak_sources {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) (w : Plane) :
    (∫ z : Plane, inner (𝕜 := ℝ)
      (gradient (fun u => green u w) z) (gradient ψ z)) = ψ w - ψ (star w) := by
  calc
    _ = ∫ z : Plane,
        inner (𝕜 := ℝ) (gradient (fundamental w) z) (gradient ψ z) -
        inner (𝕜 := ℝ) (gradient (fundamental (star w)) z) (gradient ψ z) := by
      apply integral_congr_ae
      filter_upwards [(countable_singleton w).ae_not_mem volume,
        (countable_singleton (star w)).ae_not_mem volume] with z hp hr
      have hp : z ≠ w := by simpa using hp
      have hr : z ≠ star w := by simpa using hr
      rw [green_gradient_sub_fundamental hp hr, inner_sub_left]
    _ = ψ w - ψ (star w) := by
      rw [integral_sub (fundamental_pairing_integrable_at hψ w)
        (fundamental_pairing_integrable_at hψ (star w)),
        fundamental_weak_source_at hψ, fundamental_weak_source_at hψ]

/-- The concrete half-plane Green kernel has the exact weak normalization
`-ΔG=δ_w` against every actual compact smooth half-plane test. -/
theorem green_weak_source {ψ : Plane → ℝ} (hψ : IsTest upperHalfPlane ψ)
    {w : Plane} (hw : w ∈ upperHalfPlane) :
    (∫ z in upperHalfPlane, inner (𝕜 := ℝ)
      (gradient (fun u => green u w) z) (gradient ψ z)) = ψ w := by
  have hzero : ψ (star w) = 0 := by
    by_contra h
    have hi := hψ.2.2 (subset_tsupport ψ (Function.mem_support.mpr h))
    change 0 < (star w).im at hi
    simp only [Complex.star_def, Complex.conj_im] at hi
    have hwim : 0 < w.im := hw
    linarith
  have hrestrict : (∫ z in upperHalfPlane, inner (𝕜 := ℝ)
      (gradient (fun u => green u w) z) (gradient ψ z)) =
      ∫ z : Plane, inner (𝕜 := ℝ)
        (gradient (fun u => green u w) z) (gradient ψ z) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hgrad : gradient ψ z = 0 :=
      gradient_eq_zero_of_not_mem_tsupport (fun h => hz (hψ.2.2 h))
    rw [hgrad, inner_zero_right]
  rw [hrestrict, green_weak_sources hψ, hzero, sub_zero]

end Torsion.HalfPlane

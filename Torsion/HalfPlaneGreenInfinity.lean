module

public import Torsion.HalfPlaneGreen
public import Torsion.HalfPlanePoisson

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The normalized Green source derivative at the compactified boundary -/

noncomputable section
open Set Filter
open scoped Topology

namespace Torsion.HalfPlane

/-- The nonsingular infinity-coordinate expression is exactly the concrete
Green kernel whenever the source and its reflection avoid the evaluation point. -/
theorem infinitySource_eq_green {z : Plane} {t : ℝ} (ht : t ≠ 0)
    (hp : z - (t⁻¹ : ℝ) * Complex.I ≠ 0)
    (hr : z - star ((t⁻¹ : ℝ) * Complex.I) ≠ 0) :
    infinitySource z t = green z ((t⁻¹ : ℝ) * Complex.I) := by
  have h₁ : 1 - (t : Plane) * Complex.I * z =
      (-(t : Plane) * Complex.I) *
        (z - star ((t⁻¹ : ℝ) * Complex.I)) := by
    simp only [map_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_inv]
    field_simp
    ring_nf
    simp [Complex.I_sq, ht]
    ring
  have h₂ : 1 + (t : Plane) * Complex.I * z =
      ((t : Plane) * Complex.I) * (z - (t⁻¹ : ℝ) * Complex.I) := by
    rw [Complex.ofReal_inv]
    field_simp
    ring_nf
    simp [Complex.I_sq, ht]
    ring
  have htC : (t : Plane) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  unfold infinitySource green
  rw [h₁, h₂]
  simp only [norm_mul, norm_neg, Complex.norm_I, mul_one]
  rw [Real.log_mul (norm_ne_zero_iff.mpr htC) (norm_ne_zero_iff.mpr hr),
    Real.log_mul (norm_ne_zero_iff.mpr htC) (norm_ne_zero_iff.mpr hp)]
  ring

/-- The compactifying source has the exact Green quotient coefficient
`Im(z)/π`. This is a limit of the actual two-variable logarithmic kernel. -/
theorem green_source_infinity_div_t_tendsto (z : Plane) :
    Tendsto (fun t : ℝ => green z ((t⁻¹ : ℝ) * Complex.I) / t)
      (𝓝[≠] 0) (𝓝 (z.im / Real.pi)) := by
  apply (infinitySource_div_t_tendsto z).congr'
  have hm : ContinuousAt (fun t : ℝ => 1 - (t : Plane) * Complex.I * z) 0 := by
    fun_prop
  have hp : ContinuousAt (fun t : ℝ => 1 + (t : Plane) * Complex.I * z) 0 := by
    fun_prop
  have hmne : ∀ᶠ t : ℝ in 𝓝 0, 1 - (t : Plane) * Complex.I * z ≠ 0 :=
    hm.eventually_ne (by simp)
  have hpne : ∀ᶠ t : ℝ in 𝓝 0, 1 + (t : Plane) * Complex.I * z ≠ 0 :=
    hp.eventually_ne (by simp)
  filter_upwards [self_mem_nhdsWithin, hmne.filter_mono nhdsWithin_le_nhds,
    hpne.filter_mono nhdsWithin_le_nhds] with t ht hm hp
  have ht' : t ≠ 0 := by simpa using ht
  have htC : (t : Plane) ≠ 0 := Complex.ofReal_ne_zero.mpr ht'
  rw [infinitySource_eq_green ht']
  · intro h
    apply hp
    have heq : z = (t⁻¹ : ℝ) * Complex.I := sub_eq_zero.mp h
    rw [heq, Complex.ofReal_inv]
    field_simp [htC]
    ring_nf
    simp [Complex.I_sq]
  · intro h
    apply hm
    have heq := sub_eq_zero.mp h
    rw [heq]
    simp only [map_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_inv]
    field_simp [htC]
    ring_nf
    simp [Complex.I_sq]

end Torsion.HalfPlane

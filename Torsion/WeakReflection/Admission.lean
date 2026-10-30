import Torsion.WeakReflection.Translation
import Torsion.SobolevLocalization

/-!
# Actual zero-boundary admission for a flat half-plane

A compactly supported H¹ pair that vanishes below the real axis belongs to
H¹₀ of the upper half-plane.  Translating it a positive distance upward gives
compact support strictly in that open set; strong translation continuity
then gives membership by closedness.  This argument uses the geometry of a
half-plane and makes no assertion for arbitrary slit domains.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion

theorem MemH10.upperHalfPlane_of_compact_support
    {E K : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 E u g) (hK : IsCompact K)
    (huK : ∀ᵐ z ∂volume, z ∉ K → u z = 0)
    (huLower : ∀ᵐ z ∂volume, z.im < 0 → u z = 0) :
    MemH10 upperHalfPlane u g := by
  let K₀ : Set Plane := K ∩ {z : Plane | 0 ≤ z.im}
  have hK₀ : IsCompact K₀ :=
    hK.inter_right (isClosed_le continuous_const Complex.continuous_im)
  let a : ℕ → Plane := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero, zero_mul] using
      ((Complex.continuous_ofReal.tendsto 0).comp
        tendsto_one_div_add_atTop_nhds_zero_nat).mul_const Complex.I
  have hseq (n : ℕ) : MemH10 upperHalfPlane
      (Torsion.translatedValue (a n) u) (Torsion.translatedValue (a n) g) := by
    let Kₙ : Set Plane := (fun z : Plane => z + a n) '' K₀
    have hKₙ : IsCompact Kₙ := hK₀.image (continuous_id.add continuous_const)
    have hKₙU : Kₙ ⊆ upperHalfPlane := by
      rintro z ⟨w, ⟨hwK, hwIm⟩, rfl⟩
      change 0 < (w + a n).im
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      simpa only [a, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_im, Complex.I_re, zero_mul, sub_zero, mul_one, add_zero] using
        add_pos_of_nonneg_of_pos hwIm hpos
    apply (hu.translatedValue (a n)).localize_compact_value
      (isOpen_lt continuous_const Complex.continuous_im) hKₙ hKₙU
    filter_upwards [(measurePreserving_sub_const (a n)).quasiMeasurePreserving.ae huK,
      (measurePreserving_sub_const (a n)).quasiMeasurePreserving.ae huLower] with z hzK hzLower
    intro hz
    change u (z - a n) = 0
    by_cases hmem : z - a n ∈ K
    · have him : (z - a n).im < 0 := by
        by_contra hn
        apply hz
        refine ⟨z - a n, ⟨hmem, le_of_not_gt hn⟩, ?_⟩
        exact sub_add_cancel z (a n)
      exact hzLower him
    · exact hzK hmem
  exact MemH10.of_tendsto hu.1 hu.2.1 hseq
    (tendsto_eLpNorm_translatedValue_sub hu.1 ha)
    (tendsto_eLpNorm_translatedValue_sub hu.2.1 ha)

end Torsion

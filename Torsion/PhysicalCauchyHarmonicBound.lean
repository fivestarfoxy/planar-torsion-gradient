module

public import Torsion.PhysicalCauchyHarmonicDerivative

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual uniform gradient bounds for smooth compact-data harmonic lifts

The derivative ratio extends continuously over every finite boundary point.
Actual second-kernel moments control the ratio at infinity. Compactness of
the remaining parameter region therefore supplies a genuine global bound
for the physical gradient, with no assumed boundary gradient estimate.
-/

noncomputable section
open Set Filter MeasureTheory Metric Bornology
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral

theorem cauchyDerivativeExtension_ne_zero_on_closedHalfPlane
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1, realCauchyBoundaryRe φ x = a * height φ x - b)
    {z : Plane} (hz : z ∈ closure upperHalfPlane) : cauchyDerivativeExtension φ z ≠ 0 := by
  have him : 0 ≤ z.im := by simpa [upperHalfPlane, Complex.closure_setOf_lt_im] using hz
  by_cases hzim : z.im = 0
  · have hzreal : (z.re : Plane) = z := by apply Complex.ext <;> simp [hzim]
    rw [← hzreal]
    by_cases hx : |z.re| ≤ 1
    · exact cauchyDerivativeExtension_ne_zero_on_interval ha hφ hα0 hα1 hodd hzero hpos hlinear
        (abs_le.mp hx)
    · have hp := cauchy_boundary_tangent_exterior_pos hφ hα0 hα1 hodd hzero hpos
        (lt_of_not_ge hx)
      intro hn
      simpa only [hn, Complex.zero_re, lt_self_iff_false] using hp
  · have hzH : z ∈ upperHalfPlane := lt_of_le_of_ne him (Ne.symm hzim)
    rw [cauchyDerivativeExtension_eq (hφ.continuous hα0) hodd hzero hzH]
    exact cauchy_derivative_ne_zero (hφ.continuous hα0) hodd hzero hpos hzH

private theorem bound_of_continuousOn_closure_tendsto_infinity {F : Plane → Plane} {L : Plane}
    (hF : ContinuousOn F (closure upperHalfPlane))
    (hlim : Tendsto F (cobounded Plane ⊓ 𝓟 upperHalfPlane) (𝓝 L)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ upperHalfPlane, ‖F z‖ ≤ B := by
  have he : ∀ᶠ z : Plane in cobounded Plane ⊓ 𝓟 upperHalfPlane, ‖F z‖ ≤ ‖L‖ + 1 := by
    filter_upwards [hlim.norm.eventually (gt_mem_nhds (lt_add_one ‖L‖))] with z hz
    exact hz.le
  have he' : ∀ᶠ z : Plane in cobounded Plane, z ∈ upperHalfPlane → ‖F z‖ ≤ ‖L‖ + 1 :=
    eventually_inf_principal.mp he
  obtain ⟨R, _, hR⟩ := (Filter.hasBasis_cobounded_norm (E := Plane)).mem_iff.mp he'
  let K : Set Plane := closure upperHalfPlane ∩ closedBall 0 R
  have hK : IsCompact K := (isCompact_closedBall (0 : Plane) R).inter_left isClosed_closure
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (hF.mono inter_subset_left)
  refine ⟨max 0 (max A (‖L‖ + 1)), le_max_left _ _, ?_⟩
  intro z hz
  by_cases hn : ‖z‖ ≤ R
  · exact (hA z ⟨subset_closure hz, by simpa using hn⟩).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hR (le_of_lt (lt_of_not_ge hn)) hz).trans
      ((le_max_right _ _).trans (le_max_right _ _))

theorem physicalHarmonicLift_gradient_exists_norm_bound
    {a b : ℝ} {φ g : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1, realCauchyBoundaryRe φ x = a * height φ x - b)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioo (-1 : ℝ) 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ cauchyImage φ, ‖gradient (physicalHarmonicLift φ g) w‖ ≤ B := by
  have hc := hφ.continuous hα0
  obtain ⟨hE, hEe⟩ := realCauchy_derivative_extension_of_compactSmooth hg hgc hgs
  have hD := (cauchyDerivativeExtension_diffContOnCl hφ hα0 hzero).continuousOn
  let F : Plane → Plane := fun z => realCauchyExtension (deriv g) z / cauchyDerivativeExtension φ z
  have hF : ContinuousOn F (closure upperHalfPlane) := hE.div hD
    (fun z hz => cauchyDerivativeExtension_ne_zero_on_closedHalfPlane
      ha hφ hα0 hα1 hodd hzero hpos hlinear hz)
  let l : Filter Plane := cobounded Plane ⊓ 𝓟 upperHalfPlane
  have hnorm : Tendsto (fun z : Plane => ‖z‖) l atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  have hH : ∀ᶠ z : Plane in l, z ∈ upperHalfPlane := mem_inf_of_right (by simp)
  have hM : ((Real.pi : Plane)⁻¹ * (mass φ : Plane)) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr (mass_pos hc.continuousOn hpos).ne')
  have hlim := (realCauchy_derivative_moment hg.continuous hnorm hH).div
    (cauchy_derivative_moment hc.continuousOn hnorm hH) hM
  have hFlim : Tendsto F l
      (𝓝 (((Real.pi : Plane)⁻¹ * ((∫ s in Icc (-1 : ℝ) 1, g s : ℝ) : Plane)) /
        ((Real.pi : Plane)⁻¹ * (mass φ : Plane)))) := by
    apply hlim.congr'
    filter_upwards [hH] with z hz
    dsimp only [F, Pi.div_apply]
    rw [hEe z hz, cauchyDerivativeExtension_eq hc hodd hzero hz]
    have hzne : z ≠ 0 := by intro hn; simpa [upperHalfPlane, hn] using hz
    field_simp [hzne, cauchy_derivative_ne_zero hc hodd hzero hpos hz]
  obtain ⟨B, hB0, hB⟩ := bound_of_continuousOn_closure_tendsto_infinity hF hFlim
  refine ⟨B, hB0, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  rw [(physicalHarmonicLift_hasGradientAt_cauchy hc hodd hzero hpos hg.continuous hz).gradient]
  simp only [norm_mul, Complex.norm_I, norm_star, one_mul]
  simpa only [F, hEe z hz, cauchyDerivativeExtension_eq hc hodd hzero hz] using hB z hz

end Torsion.Spectral

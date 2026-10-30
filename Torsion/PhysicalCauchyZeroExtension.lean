import Torsion.PhysicalCauchyBoundary
import Torsion.CauchyTransformImageFrontier

/-!
# The actual continuous zero extension of the physical candidate

The conformal pullback is a difference of actual Poisson integrals. It is
continuous, vanishes at every real parameter, and decays at infinity. Its
positive absolute superlevels are therefore compact subsets of H. Their
compact Cauchy images prove continuity of the physical zero extension at
every point outside the image, without a boundary-trace assumption.
-/

noncomputable section
open Set Filter MeasureTheory Bornology
open scoped Topology NNReal

namespace Torsion.Spectral

/-- A globally continuous parameter-space extension of the candidate,
written using its actual fixed Poisson kernels. -/
def physicalParameterExtension (φ : ℝ → ℝ) (z : Plane) : ℝ :=
  -(poissonExtension (height φ) z) ^ 2 / 2 +
    poissonExtension (fun s => (height φ s) ^ 2) z / 2

theorem physicalParameterExtension_continuous {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    Continuous (physicalParameterExtension φ) := by
  have hY := height_continuous hφ
  have hP := poissonExtension_continuous hY (fun s hs => height_zero_of_one_le_abs φ hs)
  have hP2 := poissonExtension_continuous (hY.pow 2)
    (fun s hs => by rw [height_zero_of_one_le_abs φ hs]; norm_num)
  exact ((hP.pow 2).neg.div_const 2).add (hP2.div_const 2)

theorem physicalParameterExtension_ofReal (φ : ℝ → ℝ) (x : ℝ) :
    physicalParameterExtension φ (x : Plane) = 0 := by
  simp only [physicalParameterExtension, poissonExtension_ofReal]
  ring

theorem physicalParameterExtension_eq_extensions (φ : ℝ → ℝ) (z : Plane) :
    physicalParameterExtension φ z = -((cauchyExtension φ z).im) ^ 2 / 2 +
      (auxiliaryExtension φ z).im := by
  simp only [physicalParameterExtension, cauchyExtension, auxiliaryExtension,
    realCauchyExtension, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, mul_one,
    zero_add, add_zero]
  norm_num
  ring

theorem physicalParameterExtension_eq_raw {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : Plane} (hz : z ∈ upperHalfPlane) :
    physicalParameterExtension φ z = -((cauchy φ z).im) ^ 2 / 2 + (auxiliary φ z).im := by
  rw [physicalParameterExtension_eq_extensions,
    cauchyExtension_eq hφ hz, auxiliaryExtension_eq hφ hz]

theorem physicalParameterExtension_eq_candidate {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    {z : Plane} (hz : z ∈ upperHalfPlane) :
    physicalParameterExtension φ z = physicalCandidate φ (cauchy φ z) := by
  rw [physicalParameterExtension_eq_raw hφ.continuousOn hz]
  simp only [physicalCandidate, PhysicalTorsion.candidate,
    physicalHolomorphic_cauchy hφ hodd hzero hpos hz]

/-- Every absolute superlevel at positive height is actually compact in
the closed half-plane. The only escape directions are eliminated by the
proved Cauchy decay; no compactness certificate is an input. -/
theorem physicalParameterExtension_superlevel_isCompact {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    IsCompact (closure upperHalfPlane ∩
      (fun z => ‖physicalParameterExtension φ z‖) ⁻¹' Ici ε) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · exact (physicalParameterExtension_continuous hφ).norm.continuousOn
      |>.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
  · have hF := (Complex.continuous_im.tendsto 0).comp
      (cauchy_tendsto_zero hφ (tendsto_norm_cobounded_atTop (E := Plane)))
    have hA := (Complex.continuous_im.tendsto 0).comp
      (auxiliary_tendsto_zero hφ (tendsto_norm_cobounded_atTop (E := Plane)))
    have hraw : Tendsto (fun z : Plane => -((cauchy φ z).im) ^ 2 / 2 + (auxiliary φ z).im)
        (cobounded Plane) (𝓝 0) := by
      simpa only [Complex.zero_im, zero_pow (by norm_num : 2 ≠ 0), neg_zero,
        zero_div, zero_add] using ((hF.pow 2).neg.div_const (2 : ℝ)).add hA
    have hgood : ∀ᶠ z : Plane in cobounded Plane,
        ‖-((cauchy φ z).im) ^ 2 / 2 + (auxiliary φ z).im‖ < ε := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        hraw.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
    have hb : IsBounded {z : Plane | ¬ ‖-((cauchy φ z).im) ^ 2 / 2 +
        (auxiliary φ z).im‖ < ε} := isBounded_compl_iff.mpr hgood
    apply hb.subset
    intro z hz
    have hznonneg : 0 ≤ z.im := by
      simpa [upperHalfPlane, Complex.closure_setOf_lt_im] using hz.1
    by_cases hzh : 0 < z.im
    · simpa only [physicalParameterExtension_eq_raw hφ hzh, mem_preimage,
        mem_Ici, not_lt] using hz.2
    · have hzi : z.im = 0 := le_antisymm (not_lt.mp hzh) hznonneg
      have hzeq : z = (z.re : Plane) := by apply Complex.ext <;> simp [hzi]
      have hlevel : ε ≤ ‖physicalParameterExtension φ z‖ := hz.2
      rw [hzeq, physicalParameterExtension_ofReal, norm_zero] at hlevel
      exact (not_le_of_gt hε hlevel).elim

theorem physicalParameterExtension_superlevel_subset {φ : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε) :
    closure upperHalfPlane ∩ (fun z => ‖physicalParameterExtension φ z‖) ⁻¹' Ici ε ⊆
      upperHalfPlane := by
  intro z hz
  have hznonneg : 0 ≤ z.im := by
    simpa [upperHalfPlane, Complex.closure_setOf_lt_im] using hz.1
  by_contra hzh
  have hzi : z.im = 0 := le_antisymm (not_lt.mp hzh) hznonneg
  have hzeq : z = (z.re : Plane) := by apply Complex.ext <;> simp [hzi]
  have hlevel : ε ≤ ‖physicalParameterExtension φ z‖ := hz.2
  rw [hzeq, physicalParameterExtension_ofReal, norm_zero] at hlevel
  exact not_le_of_gt hε hlevel

/-- The genuine global zero extension of the physical candidate. -/
def physicalZeroExtension (φ : ℝ → ℝ) : Plane → ℝ :=
  (cauchyImage φ).indicator (physicalCandidate φ)

theorem physicalZeroExtension_eq {φ : ℝ → ℝ} {w : Plane} (hw : w ∈ cauchyImage φ) :
    physicalZeroExtension φ w = physicalCandidate φ w := indicator_of_mem hw _

theorem physicalZeroExtension_eq_zero {φ : ℝ → ℝ} {w : Plane} (hw : w ∉ cauchyImage φ) :
    physicalZeroExtension φ w = 0 := indicator_of_not_mem hw _

/-- The actual zero extension is continuous everywhere. This discharges
the value-trace regularity needed for the direct H¹₀ truncation argument. -/
theorem physicalZeroExtension_continuous {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    Continuous (physicalZeroExtension φ) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ cauchyImage φ
  · have hpc := (PhysicalTorsion.candidate_hasGradientAt
      ((physicalHolomorphic_analyticOnNhd hφ hodd hzero hpos) p hp).differentiableAt).continuousAt
    apply hpc.congr_of_eventuallyEq
    filter_upwards [(cauchyImage_isOpen hφ hodd hzero hpos).mem_nhds hp] with w hw
    exact physicalZeroExtension_eq hw
  · rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    let K : Set Plane := closure upperHalfPlane ∩
      (fun z => ‖physicalParameterExtension φ z‖) ⁻¹' Ici ε
    have hK : IsCompact K := physicalParameterExtension_superlevel_isCompact hφ.continuousOn hε
    have hKH : K ⊆ upperHalfPlane := physicalParameterExtension_superlevel_subset hε
    have himage : IsCompact (cauchy φ '' K) := hK.image_of_continuousOn
      ((cauchy_differentiableOn hφ.continuousOn).continuousOn.mono hKH)
    have hpnot : p ∉ cauchy φ '' K := fun hpK => hp (image_mono hKH hpK)
    filter_upwards [himage.isClosed.isOpen_compl.mem_nhds hpnot] with w hw
    rw [physicalZeroExtension_eq_zero hp, dist_zero_right]
    by_cases hwD : w ∈ cauchyImage φ
    · rw [physicalZeroExtension_eq hwD]
      have hz := cauchyInverse_mem hwD
      have heq : physicalCandidate φ w = physicalParameterExtension φ (cauchyInverse φ w) := by
        rw [physicalParameterExtension_eq_candidate hφ hodd hzero hpos hz,
          cauchy_cauchyInverse hwD]
      rw [heq]
      by_contra! hlarge
      apply hw
      exact ⟨cauchyInverse φ w, ⟨subset_closure hz, hlarge⟩, cauchy_cauchyInverse hwD⟩
    · simpa only [physicalZeroExtension_eq_zero hwD, norm_zero] using hε

end Torsion.Spectral

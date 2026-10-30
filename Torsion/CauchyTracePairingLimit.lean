import Torsion.CauchyTransformBoundaryDerivative
import Torsion.RestrictedSpectralIntegrated

/-!
# Passing from regularized Fourier pairings to the actual Cauchy trace

Compact-test integration preserves the genuine continuous boundary limit.
The finite-energy Fourier pairing also converges under exponential damping.
These are limit theorems for the existing concrete transforms and form.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion.Spectral

/-- The concrete Hilbert trace is an actual continuous real function. -/
theorem realCauchyBoundaryRe_continuous {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) :
    Continuous (realCauchyBoundaryRe f) := by
  have h := (realCauchyReExtension_continuousOn_closure hf hα hzero).comp_continuous
    Complex.continuous_ofReal ofReal_mem_closure_upperHalfPlane
  simpa only [Function.comp_def, realCauchyReExtension_ofReal] using h

/-- Integration against a genuine compact smooth interval test commutes
with the vertical limit of the real Cauchy transform. -/
theorem realCauchy_pairing_tendsto_boundary {f ψ : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) (hψ : IsCore ψ) :
    Tendsto (fun y : ℝ => ∫ x : ℝ,
      ψ x * (realCauchy f ((x : ℂ) + (y : ℂ) * Complex.I)).re)
      (𝓝[>] 0) (𝓝 (∫ x : ℝ, ψ x * realCauchyBoundaryRe f x)) := by
  let g : ℝ → ℝ → ℝ := fun y x => ψ x *
    subtractedRealCauchy f 3 ((x : ℂ) + (y : ℂ) * Complex.I)
  have hg : Continuous g.uncurry := by
    exact (hψ.1.continuous.comp continuous_snd).mul
      ((subtractedRealCauchy_continuous hf hα (by norm_num : (0 : ℝ) ≤ 3)).comp
        ((Complex.continuous_ofReal.comp continuous_snd).add
          ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)))
  have hI : Continuous (fun y : ℝ => ∫ x in Icc (-1 : ℝ) 1, g y x) :=
    continuous_parametric_integral_of_continuous hg isCompact_Icc
  have hzψ (x : ℝ) (hx : x ∉ Icc (-1 : ℝ) 1) : ψ x = 0 :=
    image_eq_zero_of_nmem_tsupport (fun h => hx (Ioo_subset_Icc_self (hψ.2.2 h)))
  have hR (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : 1 + |x| ≤ 3 := by
    have ha : |x| ≤ 1 := abs_le.mpr hx
    linarith
  have hzeroI : (∫ x in Icc (-1 : ℝ) 1, g 0 x) =
      ∫ x : ℝ, ψ x * realCauchyBoundaryRe f x := by
    calc
      _ = ∫ x in Icc (-1 : ℝ) 1, ψ x * realCauchyBoundaryRe f x := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        dsimp only [g]
        simp only [Complex.ofReal_zero, zero_mul, add_zero]
        rw [subtractedRealCauchy_radius_independent hf hα hzero x (hR x hx)]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hzψ x hx, zero_mul])
  have hlim : Tendsto (fun y : ℝ => ∫ x in Icc (-1 : ℝ) 1, g y x)
      (𝓝[>] 0) (𝓝 (∫ x in Icc (-1 : ℝ) 1, g 0 x)) :=
    hI.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [hzeroI] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  calc
    (∫ x in Icc (-1 : ℝ) 1, g y x) = ∫ x in Icc (-1 : ℝ) 1,
        ψ x * (realCauchy f ((x : ℂ) + (y : ℂ) * Complex.I)).re := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      dsimp only [g]
      congr 1
      apply (realCauchy_re_eq_subtracted (hf.continuous hα) hzero
        (by simpa [upperHalfPlane] using hy) _).symm
      simpa using hR x hx
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hzψ x hx, zero_mul])

/-- Exponential damping tends to the actual finite-energy Fourier form.
No Hilbert multiplier identification is used in this convergence theorem. -/
theorem damped_energy_tendsto {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hef : FiniteEnergy f) (heg : FiniteEnergy g) :
    Tendsto (fun y : ℝ => (1 / (2 * Real.pi)) * ∫ ξ : ℝ,
      Real.exp (-y * |ξ|) * |ξ| * (fourier f ξ * star (fourier g ξ)).re)
      (𝓝[>] 0) (𝓝 (energy f g)) := by
  let G : ℝ → ℝ := fun ξ => |ξ| * (fourier f ξ * star (fourier g ξ)).re
  have hG : Integrable G := energy_integrand_integrable hf hg hef heg
  have hmeas (y : ℝ) : AEStronglyMeasurable (fun ξ : ℝ => Real.exp (-y * |ξ|) * G ξ) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable.mul
      hG.aestronglyMeasurable
  have hbound : ∀ᶠ y : ℝ in 𝓝[>] 0,
      ∀ᵐ ξ : ℝ, ‖Real.exp (-y * |ξ|) * G ξ‖ ≤ ‖G ξ‖ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ae_of_all _ fun ξ => by
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
      apply mul_le_of_le_one_left (norm_nonneg _)
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hy)) (abs_nonneg _)
  have hpoint : ∀ᵐ ξ : ℝ, Tendsto (fun y : ℝ => Real.exp (-y * |ξ|) * G ξ)
      (𝓝[>] 0) (𝓝 (G ξ)) := by
    exact ae_of_all _ fun ξ => by
      have hc : ContinuousAt (fun y : ℝ => Real.exp (-y * |ξ|) * G ξ) 0 := by fun_prop
      simpa using hc.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hi := tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖G ξ‖)
    (Eventually.of_forall hmeas) hbound hG.norm hpoint
  have hm := hi.const_mul (1 / (2 * Real.pi))
  simpa only [G, energy, mul_assoc] using hm

end Torsion.Spectral

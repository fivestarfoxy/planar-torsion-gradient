module

public import Torsion.RestrictedSpectralTestPartition
public import Torsion.RestrictedSpectralExteriorTest

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual whole-line weak restricted spectral equation

Genuine endpoint cutoffs split every Schwartz test into an original
interior core and an exterior Schwartz test. Their original Fourier
energy pairings vanish weakly, while bounded shrinking supports vanish
against the actual L¹ residual. Thus no endpoint distributions remain.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff SchwartzMap

namespace Torsion.Spectral

theorem integrable_mul_schwartz {q : ℝ → ℝ} (hq : Integrable q) (S : 𝓢(ℝ, ℝ)) :
    Integrable (fun x : ℝ => q x * S x) := by
  have h := hq.bdd_mul S.continuous.aestronglyMeasurable
    (ae_of_all _ fun x => SchwartzMap.norm_le_seminorm ℝ S x)
  simpa only [mul_comm] using h

/-- Actual Fourier energy against real Schwartz tests is linear. -/
def schwartzEnergyFunctional (f : ℝ → ℝ) (hf : Integrable f) (hef : FiniteEnergy f) :
    𝓢(ℝ, ℝ) →ₗ[ℝ] ℝ where
  toFun S := energy f S
  map_add' S T := energy_add_right hf S.integrable T.integrable hef
    (finiteEnergy_of_schwartz S) (finiteEnergy_of_schwartz T)
  map_smul' c S := energy_const_mul_right f S c

/-- Integration against the actual L¹ density is linear on Schwartz tests. -/
def schwartzPairFunctional (q : ℝ → ℝ) (hq : Integrable q) : 𝓢(ℝ, ℝ) →ₗ[ℝ] ℝ where
  toFun S := ∫ x : ℝ, q x * S x
  map_add' S T := by
    change (∫ x : ℝ, q x * (S x + T x)) = _
    simp_rw [mul_add]
    exact integral_add (integrable_mul_schwartz hq S) (integrable_mul_schwartz hq T)
  map_smul' c S := by
    change (∫ x : ℝ, q x * (c * S x)) = c * ∫ x : ℝ, q x * S x
    simp_rw [mul_left_comm (q _) c]
    exact integral_const_mul c _

/-- The actual density on the full real line, with its zero-extended
exterior residual. -/
def globalSpectralDensity (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  a * f x - exteriorResidualZero f x

theorem globalSpectralDensity_integrable {a : ℝ} {f : ℝ → ℝ}
    (hf : Integrable f) (hr : Integrable (exteriorResidualZero f)) :
    Integrable (globalSpectralDensity a f) := (hf.const_mul a).sub hr

/-- The original weak eigenfunction equation is already the full density
identity on every genuine interior Schwartz/core test. -/
theorem IsRestrictedEigenfunction.schwartz_core_density_equation
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hr : Integrable (exteriorResidualZero f)) (S : 𝓢(ℝ, ℝ)) (hS : IsCore S) :
    energy f S = ∫ x : ℝ, globalSpectralDensity a f x * S x := by
  have hfi := integrable_mul_schwartz hf.1.integrable S
  have hri := integrable_mul_schwartz hr S
  have hz : (fun x : ℝ => exteriorResidualZero f x * S x) = 0 := by
    funext x
    by_cases hx : 1 < |x|
    · have hn : x ∉ tsupport S := by
        intro hs
        have hi := abs_lt.2 (hS.2.2 hs)
        linarith
      rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]
      rfl
    · simp only [exteriorResidualZero, if_neg hx, zero_mul, Pi.zero_apply]
  rw [hf.2.2 S hS.memRestrictedFormDomain]
  simp only [globalSpectralDensity, sub_mul, mul_assoc]
  rw [integral_sub (hfi.const_mul a) hri, integral_const_mul, hz]
  rw [integral_zero', sub_zero]

/-- The separated exterior test identity is exactly the same full density
identity; the original restricted datum vanishes there almost everywhere. -/
theorem IsRestrictedEigenfunction.schwartz_exterior_density_equation
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hr : Integrable (exteriorResidualZero f)) (S : 𝓢(ℝ, ℝ))
    (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < 1 + δ → S x = 0) :
    energy f S = ∫ x : ℝ, globalSpectralDensity a f x * S x := by
  obtain ⟨δ, hδ, hzero⟩ := hgap
  have hfi := integrable_mul_schwartz hf.1.integrable S
  have hri := integrable_mul_schwartz hr S
  have hz : ∫ x : ℝ, f x * S x = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hf.1.2.2.1] with x hx
    change f x * S x = 0
    by_cases hi : x ∈ Ioo (-1 : ℝ) 1
    · rw [hzero x (by have h := abs_lt.2 hi; linarith), mul_zero]
    · rw [hx hi, zero_mul]
  rw [hf.1.energy_schwartz_exterior S ⟨δ, hδ, hzero⟩]
  simp only [globalSpectralDensity, sub_mul, mul_assoc]
  rw [integral_sub (hfi.const_mul a) hri, integral_const_mul, hz, mul_zero, zero_sub]

/-- The actual trimmed Schwartz test satisfies the full operator identity
by its proved core/exterior partition. -/
theorem IsRestrictedEigenfunction.endpointTrim_density_equation
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hr : Integrable (exteriorResidualZero f)) (S : 𝓢(ℝ, ℝ)) (n : ℕ) :
    energy f (endpointTrimSchwartz S n) =
      ∫ x : ℝ, globalSpectralDensity a f x * endpointTrimSchwartz S n x := by
  let E := schwartzEnergyFunctional f hf.1.integrable hf.1.2.1
  let Q := schwartzPairFunctional (globalSpectralDensity a f)
    (globalSpectralDensity_integrable hf.1.integrable hr)
  have hu : E (interiorTrimSchwartz S n) = Q (interiorTrimSchwartz S n) :=
    hf.schwartz_core_density_equation hr (interiorTrimSchwartz S n)
      (interiorTestPart_endpointTrim_isCore S.smooth' n)
  have he : E (exteriorTrimSchwartz S n) = Q (exteriorTrimSchwartz S n) :=
    hf.schwartz_exterior_density_equation hr (exteriorTrimSchwartz S n) (exteriorTrimSchwartz_gap S n)
  have hsplit : endpointTrimSchwartz S n = interiorTrimSchwartz S n + exteriorTrimSchwartz S n := by
    ext x
    exact (interiorTrimSchwartz_add_exteriorTrimSchwartz S n x).symm
  change E (endpointTrimSchwartz S n) = Q (endpointTrimSchwartz S n)
  rw [hsplit, map_add, map_add, hu, he]

/-- Every actual real Schwartz test satisfies the whole-line weak
restricted spectral equation. The endpoint cutoff contributions vanish
by the proved actual Fourier-energy and L¹ limits, excluding endpoint
Dirac or other unsupported boundary terms. -/
theorem IsRestrictedEigenfunction.global_schwartz_equation
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f)
    (hr : Integrable (exteriorResidualZero f)) (S : 𝓢(ℝ, ℝ)) :
    energy f S = ∫ x : ℝ, (a * f x - exteriorResidualZero f x) * S x := by
  let q := globalSpectralDensity a f
  have hq : Integrable q := globalSpectralDensity_integrable hf.1.integrable hr
  let E := schwartzEnergyFunctional f hf.1.integrable hf.1.2.1
  let Q := schwartzPairFunctional q hq
  let F : 𝓢(ℝ, ℝ) →ₗ[ℝ] ℝ := E - Q
  have htrim (n : ℕ) : F (endpointTrimSchwartz S n) = 0 := by
    change energy f (endpointTrimSchwartz S n) -
      (∫ x : ℝ, q x * endpointTrimSchwartz S n x) = 0
    exact sub_eq_zero.2 (hf.endpointTrim_density_equation hr S n)
  obtain ⟨A, _, hA⟩ := schwartz_exists_uniform_bound S
  obtain ⟨D, _, hD⟩ := schwartz_deriv_exists_uniform_bound S
  have hAn : ∀ x : ℝ, ‖S x‖ ≤ A := by simpa only [Real.norm_eq_abs] using hA
  have hDn : ∀ x : ℝ, ‖deriv S x‖ ≤ D := by simpa only [Real.norm_eq_abs] using hD
  have hcut (e : ℝ) : Tendsto (fun n => F
      (compactSmoothRealSchwartz (endpointCutoff_contDiff S.smooth' e (n + 3))
        (endpointCutoff_hasCompactSupport S e (n + 3)))) atTop (𝓝 0) := by
    have hE := (energy_endpointCutoff_tendsto_zero hf.1.integrable hf.1.2.1 S.smooth' hAn hDn e).comp
      (tendsto_add_atTop_nat 3)
    have hQ := (integral_mul_endpointCutoff_tendsto_zero hq S e).comp (tendsto_add_atTop_nat 3)
    simpa only [sub_zero, F, E, Q, schwartzEnergyFunctional, schwartzPairFunctional,
      LinearMap.sub_apply, Function.comp_apply] using! hE.sub hQ
  have hleft : Tendsto (fun n => F (endpointTrimSchwartz S n)) atTop (𝓝 0) := by
    simpa only [htrim] using (tendsto_const_nhds (x := (0 : ℝ)))
  have hright : Tendsto (fun n => F (endpointTrimSchwartz S n)) atTop (𝓝 (F S)) := by
    have h := (tendsto_const_nhds (x := F S)).sub (hcut 1) |>.sub (hcut (-1))
    simpa only [endpointTrimSchwartz, map_sub, sub_zero] using h
  have hz : F S = 0 := (tendsto_nhds_unique hleft hright).symm
  change energy f S - (∫ x : ℝ, (a * f x - exteriorResidualZero f x) * S x) = 0 at hz
  exact sub_eq_zero.1 hz

end Torsion.Spectral

import Torsion.RestrictedSpectralGraph
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# The genuine Hilbert space of the restricted Fourier form

The closed graph is transported to the standard Hilbert product of its real
value L² space and complex frequency L² space. Its form is the actual
frequency pairing with the original `1/(2π)` factor; coercivity follows from
the proved fractional Poincaré estimate.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform

namespace Torsion.Spectral.RestrictedHilbert

abbrev ValueL2 := Lp ℝ 2 (volume : Measure ℝ)
abbrev FrequencyL2 := Lp ℂ 2 (volume : Measure ℝ)
abbrev Ambient := WithLp 2 RestrictedSpectralPair

/-- The original pair graph and its Hilbert product carry equivalent norms. -/
def pairEquiv : Ambient ≃L[ℝ] RestrictedSpectralPair :=
  WithLp.prodContinuousLinearEquiv 2 ℝ _ _

/-- The actual complete restricted Fourier graph as a real Hilbert space. -/
def space : Submodule ℝ Ambient :=
  restrictedFormGraph.comap pairEquiv.toLinearMap

theorem isClosed_space : IsClosed (space : Set Ambient) :=
  isClosed_restrictedFormGraph.preimage pairEquiv.continuous

instance : CompleteSpace space := isClosed_space.completeSpace_coe

/-- The original value/half-derivative graph point. -/
def graphPoint (p : space) : restrictedFormGraph := ⟨pairEquiv p.1, p.2⟩

/-- The actual real L² value coordinate. -/
def valueMap : space →L[ℝ] ValueL2 :=
  (ContinuousLinearMap.fst ℝ ValueL2 FrequencyL2).comp
    (pairEquiv.toContinuousLinearMap.comp space.subtypeL)

/-- The actual complex L² half-derivative coordinate. -/
def halfMap : space →L[ℝ] FrequencyL2 :=
  (ContinuousLinearMap.snd ℝ ValueL2 FrequencyL2).comp
    (pairEquiv.toContinuousLinearMap.comp space.subtypeL)

theorem norm_sq (p : space) :
    ‖p‖ ^ 2 = ‖valueMap p‖ ^ 2 + ‖halfMap p‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 p.1

theorem half_norm_le (p : space) : ‖halfMap p‖ ≤ ‖p‖ := by
  have h := norm_sq p
  nlinarith [sq_nonneg ‖valueMap p‖, norm_nonneg (halfMap p), norm_nonneg p]

/-- The concrete fractional Poincaré estimate on a core graph point. -/
theorem core_graph_coordinate_bound {f : ℝ → ℝ} (hf : IsCore f) :
    ‖hf.spectralGraph.1‖ ^ 2 ≤ (4 / Real.pi ^ 2) * ‖hf.spectralGraph.2‖ ^ 2 := by
  have h := hf.fractional_poincare
  rw [integral_sq_eq_norm_toLp_sq hf.memLp_value,
    energy_self_eq_norm_halfDerivative hf.integrable_value hf.finiteEnergy] at h
  have hfac : (8 / Real.pi) * (1 / (2 * Real.pi)) = 4 / Real.pi ^ 2 := by
    field_simp [Real.pi_ne_zero]
    ring
  simpa only [IsCore.spectralGraph, ← mul_assoc, hfac] using h

/-- Coercivity survives the actual graph closure by continuity of the two
coordinate norms, without assuming an abstract fractional Poincaré law. -/
theorem coordinate_bound (p : space) :
    ‖valueMap p‖ ^ 2 ≤ (4 / Real.pi ^ 2) * ‖halfMap p‖ ^ 2 := by
  let C : Set RestrictedSpectralPair :=
    {q | ‖q.1‖ ^ 2 ≤ (4 / Real.pi ^ 2) * ‖q.2‖ ^ 2}
  have hclosed : IsClosed C := isClosed_le (continuous_fst.norm.pow 2)
    (continuous_const.mul (continuous_snd.norm.pow 2))
  have hsub : (restrictedCoreGraph : Set RestrictedSpectralPair) ⊆ C := by
    rintro q ⟨f, hf, rfl⟩
    exact core_graph_coordinate_bound hf
  exact closure_minimal hsub hclosed p.2

/-- The bounded bilinear form is the actual frequency Hilbert pairing,
with exactly the original source normalization. -/
def energy : space →L[ℝ] space →L[ℝ] ℝ :=
  (1 / (2 * Real.pi)) • LinearMap.mkContinuous₂
    ((innerₗ FrequencyL2).compl₁₂ halfMap.toLinearMap halfMap.toLinearMap)
    1 (by
      intro p q
      change ‖inner (𝕜 := ℝ) (halfMap p) (halfMap q)‖ ≤ 1 * ‖p‖ * ‖q‖
      simpa only [one_mul] using (norm_inner_le_norm (halfMap p) (halfMap q)).trans
        (mul_le_mul (half_norm_le p) (half_norm_le q) (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem energy_apply (p q : space) :
    energy p q = (1 / (2 * Real.pi)) * inner (𝕜 := ℝ) (halfMap p) (halfMap q) := rfl

/-- Coercivity of the actual restricted form on the actual complete graph. -/
theorem energy_coercive : IsCoercive energy := by
  have hK : 0 < (1 / (2 * Real.pi) : ℝ) := by positivity
  have hden : 0 < 4 / Real.pi ^ 2 + 1 := by positivity
  refine ⟨(1 / (2 * Real.pi)) / (4 / Real.pi ^ 2 + 1), div_pos hK hden, ?_⟩
  intro p
  rw [energy_apply, real_inner_self_eq_norm_sq]
  have htotal : ‖p‖ ^ 2 ≤ (4 / Real.pi ^ 2 + 1) * ‖halfMap p‖ ^ 2 := by
    rw [norm_sq]
    nlinarith [coordinate_bound p]
  calc
    _ = (1 / (2 * Real.pi)) * (‖p‖ ^ 2 / (4 / Real.pi ^ 2 + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((div_le_iff₀ hden).mpr (by simpa only [mul_comm] using htotal)) hK.le

/-- Actual graph coordinates satisfy the original concrete restricted
form-domain predicate, including its original core approximating sequence. -/
theorem memRestrictedFormDomain_coordinates (p : space) :
    MemRestrictedFormDomain (valueMap p : ℝ → ℝ) :=
  (restrictedFormGraph_coordinates (graphPoint p)).1

/-- The frequency coordinate is a representative of the actual weighted
Fourier integral of the value coordinate. -/
theorem halfMap_ae (p : space) :
    (halfMap p : ℝ → ℂ) =ᵐ[volume] weightedFourier (valueMap p : ℝ → ℝ) :=
  (restrictedFormGraph_coordinates (graphPoint p)).2

/-- The frequency coordinate equals the genuine half derivative L² class. -/
theorem halfMap_eq_halfDerivative (p : space) :
    halfMap p = halfDerivative (valueMap p : ℝ → ℝ)
      (memRestrictedFormDomain_coordinates p).integrable
      (memRestrictedFormDomain_coordinates p).2.1 := by
  apply Lp.ext
  exact (halfMap_ae p).trans
    (halfDerivative_ae _ (memRestrictedFormDomain_coordinates p).integrable
      (memRestrictedFormDomain_coordinates p).2.1).symm

/-- Every original form-domain function determines an element of the
actual complete Hilbert graph. -/
def ofMemRestrictedFormDomain {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) : space :=
  ⟨pairEquiv.symm (hf.1.toLp f, halfDerivative f hf.integrable hf.2.1), by
    change pairEquiv (pairEquiv.symm (hf.1.toLp f, halfDerivative f hf.integrable hf.2.1)) ∈
      restrictedFormGraph
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hf.mem_restrictedFormGraph⟩

@[simp] theorem valueMap_ofMemRestrictedFormDomain {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) :
    valueMap (ofMemRestrictedFormDomain hf) = hf.1.toLp f := rfl

@[simp] theorem halfMap_ofMemRestrictedFormDomain {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) :
    halfMap (ofMemRestrictedFormDomain hf) = halfDerivative f hf.integrable hf.2.1 := rfl

/-- The complete graph's bounded bilinear form is exactly the original
source-normalized Fourier integral on its actual value representatives. -/
theorem energy_eq_original (p q : space) :
    energy p q = Torsion.Spectral.energy (valueMap p : ℝ → ℝ) (valueMap q : ℝ → ℝ) := by
  rw [energy_apply, Torsion.Spectral.energy_eq_inner_halfDerivative
    (memRestrictedFormDomain_coordinates p).integrable
    (memRestrictedFormDomain_coordinates q).integrable
    (memRestrictedFormDomain_coordinates p).2.1
    (memRestrictedFormDomain_coordinates q).2.1,
    halfMap_eq_halfDerivative p, halfMap_eq_halfDerivative q]

/-- Evaluating the Hilbert form on original form-domain functions gives
the original concrete Fourier energy directly. -/
@[simp] theorem energy_ofMemRestrictedFormDomain {f g : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hg : MemRestrictedFormDomain g) :
    energy (ofMemRestrictedFormDomain hf) (ofMemRestrictedFormDomain hg) =
      Torsion.Spectral.energy f g := by
  rw [energy_apply, halfMap_ofMemRestrictedFormDomain, halfMap_ofMemRestrictedFormDomain,
    Torsion.Spectral.energy_eq_inner_halfDerivative hf.integrable hg.integrable hf.2.1 hg.2.1]

/-- Original admissible tests can be inserted into the graph variational
form without changing the actual Fourier pairing. -/
theorem energy_eq_original_right (p : space) {g : ℝ → ℝ}
    (hg : MemRestrictedFormDomain g) :
    energy p (ofMemRestrictedFormDomain hg) =
      Torsion.Spectral.energy (valueMap p : ℝ → ℝ) g := by
  rw [energy_apply, halfMap_ofMemRestrictedFormDomain, halfMap_eq_halfDerivative p,
    Torsion.Spectral.energy_eq_inner_halfDerivative
      (memRestrictedFormDomain_coordinates p).integrable hg.integrable
      (memRestrictedFormDomain_coordinates p).2.1 hg.2.1]

/-- An actual graph point is determined by its value. The closure has no
spurious pure-frequency components. -/
theorem valueMap_injective : Function.Injective valueMap := by
  intro p q hpq
  have hhalf : halfMap p = halfMap q := by
    apply Lp.ext
    have hp : (halfMap p : ℝ → ℂ) =ᵐ[volume] weightedFourier (valueMap q : ℝ → ℝ) := by
      simpa only [hpq] using halfMap_ae p
    exact hp.trans (halfMap_ae q).symm
  apply Subtype.ext
  apply pairEquiv.injective
  exact Prod.ext hpq hhalf

end Torsion.Spectral.RestrictedHilbert

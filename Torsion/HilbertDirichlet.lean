import Torsion.SobolevGraph
import Torsion.SobolevSupport
import Torsion.Poincare
import Torsion.BoundedDomains
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Construction of the actual weak Dirichlet solution

The concrete smooth value/gradient graph is transported to the `ℓ²` product
of the two actual `L²` spaces. Its closed subspace is a real Hilbert space.
The proved Poincaré estimate makes the gradient energy coercive, and the
Lax--Milgram theorem produces the weak torsion solution.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace Torsion.HilbertDirichlet

abbrev ValueL2 := Lp ℝ 2 (volume : Measure Plane)
abbrev GradientL2 := Lp Plane 2 (volume : Measure Plane)
abbrev Ambient := WithLp 2 SobolevPair

/-- The equivalence from the Hilbert-product norm to the original graph norm. -/
def pairEquiv : Ambient ≃L[ℝ] SobolevPair := WithLp.prodContinuousLinearEquiv 2 ℝ _ _

/-- The actual H¹₀ graph as a closed subspace of a Hilbert space. -/
def space (D : Set Plane) : Submodule ℝ Ambient :=
  (H10Graph D).comap pairEquiv.toLinearMap

theorem isClosed_space (D : Set Plane) : IsClosed (space D : Set Ambient) :=
  (isClosed_H10Graph D).preimage pairEquiv.continuous

instance (D : Set Plane) : CompleteSpace (space D) := (isClosed_space D).completeSpace_coe

/-- The original graph point of an element of the Hilbert space. -/
def graphPoint {D : Set Plane} (p : space D) : H10Graph D := ⟨pairEquiv p.1, p.2⟩

/-- Its value coordinate as a continuous linear map. -/
def valueMap (D : Set Plane) : space D →L[ℝ] ValueL2 :=
  (ContinuousLinearMap.fst ℝ ValueL2 GradientL2).comp
    (pairEquiv.toContinuousLinearMap.comp (space D).subtypeL)

/-- Its gradient coordinate as a continuous linear map. -/
def gradientMap (D : Set Plane) : space D →L[ℝ] GradientL2 :=
  (ContinuousLinearMap.snd ℝ ValueL2 GradientL2).comp
    (pairEquiv.toContinuousLinearMap.comp (space D).subtypeL)

/-- These coordinates satisfy the exact original smooth-closure definition. -/
theorem memH10_coordinates {D : Set Plane} (p : space D) :
    MemH10 D (valueMap D p : Plane → ℝ) (gradientMap D p : Plane → Plane) :=
  H10Graph.memH10_coe (graphPoint p)

/-- Squared Hilbert norm is the sum of the two physical `L²` squared norms. -/
theorem norm_sq (D : Set Plane) (p : space D) :
    ‖p‖ ^ 2 = ‖valueMap D p‖ ^ 2 + ‖gradientMap D p‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 p.1

/-- Each gradient coordinate is bounded by the full H¹ Hilbert norm. -/
theorem gradient_norm_le (D : Set Plane) (p : space D) : ‖gradientMap D p‖ ≤ ‖p‖ := by
  have h := norm_sq D p
  have hv := sq_nonneg ‖valueMap D p‖
  have hgp := norm_nonneg (gradientMap D p)
  have hp := norm_nonneg p
  nlinarith

/-- The actual bounded bilinear Dirichlet form. -/
def energy (D : Set Plane) : space D →L[ℝ] space D →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    ((innerₗ GradientL2).compl₁₂ (gradientMap D).toLinearMap (gradientMap D).toLinearMap)
    1 (by
      intro p q
      change ‖inner (𝕜 := ℝ) (gradientMap D p) (gradientMap D q)‖ ≤ 1 * ‖p‖ * ‖q‖
      simpa only [one_mul] using (norm_inner_le_norm (gradientMap D p) (gradientMap D q)).trans
        (mul_le_mul (gradient_norm_le D p) (gradient_norm_le D q)
          (norm_nonneg _) (norm_nonneg _)))

@[simp]
theorem energy_apply (D : Set Plane) (p q : space D) :
    energy D p q = inner (𝕜 := ℝ) (gradientMap D p) (gradientMap D q) := rfl

/-- Poincaré's estimate in the norm of the actual `L²` coordinates. -/
theorem exists_coordinate_bound (D : ConvexDomain) :
    ∃ K : ℝ, 0 < K ∧ ∀ p : space D.carrier,
      ‖valueMap D.carrier p‖ ≤ K * ‖gradientMap D.carrier p‖ := by
  obtain ⟨K, hK, hp⟩ := exists_poincare_constant D
  refine ⟨K, hK, ?_⟩
  intro p
  have hb := hp _ _ (memH10_coordinates p)
  have hfinite : ENNReal.ofReal K *
      eLpNorm (gradientMap D.carrier p) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)
  have hreal := ENNReal.toReal_mono hfinite hb
  simpa only [Lp.norm_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK.le] using hreal

/-- Coercivity is proved from Poincaré, rather than supplied as a PDE axiom. -/
theorem energy_coercive (D : ConvexDomain) : IsCoercive (energy D.carrier) := by
  obtain ⟨K, hK, hp⟩ := exists_coordinate_bound D
  have hden : 0 < K ^ 2 + 1 := by positivity
  refine ⟨1 / (K ^ 2 + 1), div_pos zero_lt_one hden, ?_⟩
  intro p
  rw [energy_apply, real_inner_self_eq_norm_sq]
  have hs : ‖valueMap D.carrier p‖ ^ 2 ≤ K ^ 2 * ‖gradientMap D.carrier p‖ ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg (valueMap D.carrier p))
      (mul_nonneg hK.le (norm_nonneg (gradientMap D.carrier p)))).2 (hp p)
    simpa only [mul_pow] using h
  have htotal : ‖p‖ ^ 2 ≤ (K ^ 2 + 1) * ‖gradientMap D.carrier p‖ ^ 2 := by
    rw [norm_sq]
    nlinarith
  calc
    1 / (K ^ 2 + 1) * ‖p‖ * ‖p‖ = ‖p‖ ^ 2 / (K ^ 2 + 1) := by ring
    _ ≤ ‖gradientMap D.carrier p‖ ^ 2 := (div_le_iff₀ hden).2 (by nlinarith [htotal])

/-- Integration against the source `1` on the physical domain is continuous. -/
def forcing (D : ConvexDomain) : space D.carrier →L[ℝ] ℝ :=
  (innerSL ℝ (indicatorConstLp 2 D.isOpen.measurableSet D.bounded.measure_lt_top.ne (1 : ℝ))).comp
    (valueMap D.carrier)

/-- The forcing functional is exactly the right side of (1.1). -/
theorem forcing_apply (D : ConvexDomain) (p : space D.carrier) :
    forcing D p = ∫ x in D.carrier, valueMap D.carrier p x :=
  L2.inner_indicatorConstLp_one D.isOpen.measurableSet D.bounded.measure_lt_top.ne _

/-- Actual Lax--Milgram existence on the concrete H¹₀ Hilbert graph. -/
theorem exists_variational_solution (D : ConvexDomain) :
    ∃ p : space D.carrier, ∀ q : space D.carrier,
      energy D.carrier p q = forcing D q := by
  let coercive := energy_coercive D
  let f := (InnerProductSpace.toDual ℝ (space D.carrier)).symm (forcing D)
  let p := coercive.continuousLinearEquivOfBilin.symm f
  refine ⟨p, ?_⟩
  intro q
  calc
    energy D.carrier p q = inner (𝕜 := ℝ) (coercive.continuousLinearEquivOfBilin p) q :=
      (coercive.continuousLinearEquivOfBilin_apply p q).symm
    _ = inner (𝕜 := ℝ) f q := by rw [ContinuousLinearEquiv.apply_symm_apply]
    _ = forcing D q := InnerProductSpace.toDual_symm_apply

/-- Every admissible concrete pair determines an element of the Hilbert graph. -/
def ofMemH10 {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) : space D :=
  ⟨pairEquiv.symm (hu.1.toLp u, hu.2.1.toLp g), by
    change pairEquiv (pairEquiv.symm (hu.1.toLp u, hu.2.1.toLp g)) ∈ H10Graph D
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (memH10_iff_mem_H10Graph hu.1 hu.2.1).mp hu⟩

@[simp]
theorem valueMap_ofMemH10 {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) : valueMap D (ofMemH10 hu) = hu.1.toLp u := rfl

@[simp]
theorem gradientMap_ofMemH10 {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) : gradientMap D (ofMemH10 hu) = hu.2.1.toLp g := rfl

/-- The global `L²` bilinear form is the physical-domain Dirichlet energy:
zero extension outside the domain follows from the proved graph closure. -/
theorem energy_eq_setIntegral (D : ConvexDomain) (p q : space D.carrier) :
    energy D.carrier p q = ∫ x in D.carrier,
      inner (𝕜 := ℝ) (gradientMap D.carrier p x) (gradientMap D.carrier q x) := by
  rw [energy_apply, L2.inner_def,
    ← integral_add_compl D.isOpen.measurableSet (L2.integrable_inner _ _)]
  have hzero : (∫ x in D.carrierᶜ,
      inner (𝕜 := ℝ) (gradientMap D.carrier p x) (gradientMap D.carrier q x)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [(memH10_coordinates p).gradient_ae_zero_off] with x hx
    simp only [Pi.zero_apply] at hx
    simp [hx]
  rw [hzero, add_zero]

/-- Extraction yields the original weak equation for every actual `MemH10`
test pair, not merely for an auxiliary finite-dimensional test space. -/
theorem variational_isWeakTorsion (D : ConvexDomain) (p : space D.carrier)
    (hp : ∀ q : space D.carrier, energy D.carrier p q = forcing D q) :
    IsWeakTorsion D.carrier (valueMap D.carrier p) (gradientMap D.carrier p) := by
  refine ⟨memH10_coordinates p, ?_⟩
  intro v h hv
  have heq := hp (ofMemH10 hv)
  rw [energy_eq_setIntegral, forcing_apply, valueMap_ofMemH10, gradientMap_ofMemH10] at heq
  calc
    (∫ x in D.carrier, inner (𝕜 := ℝ) (gradientMap D.carrier p x) (h x)) =
        ∫ x in D.carrier, inner (𝕜 := ℝ) (gradientMap D.carrier p x) (hv.2.1.toLp h x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hv.2.1.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x in D.carrier, hv.1.toLp v x := heq
    _ = ∫ x in D.carrier, v x := by
      apply integral_congr_ae
      exact ae_restrict_of_ae hv.1.coeFn_toLp

/-- Existence of actual weak torsion solutions on every bounded open convex
domain is now proved from the concrete definitions and Poincaré inequality. -/
theorem exists_dirichletSolution (D : ConvexDomain) : Nonempty (DirichletSolution D.carrier) := by
  obtain ⟨p, hp⟩ := exists_variational_solution D
  exact ⟨⟨valueMap D.carrier p, gradientMap D.carrier p, variational_isWeakTorsion D p hp⟩⟩

/-- A chosen actual weak solution, with its proved weak equation. -/
def solution (D : ConvexDomain) : DirichletSolution D.carrier :=
  Classical.choice (exists_dirichletSolution D)

/-- The previously hypothetical weak Dirichlet theory is inhabited. -/
def dirichletTheory : DirichletTheory := ⟨solution⟩

/-! ## Bounded measurable domains, without convexity or boundary regularity -/

/-- Poincaré controls the coordinates of the actual Hilbert graph on every
bounded set; openness, convexity and nonemptiness are unnecessary. -/
theorem exists_coordinate_bound_of_bounded {D : Set Plane} (hD : Bornology.IsBounded D) :
    ∃ K : ℝ, 0 < K ∧ ∀ p : space D, ‖valueMap D p‖ ≤ K * ‖gradientMap D p‖ := by
  obtain ⟨K, hK, hp⟩ := exists_poincare_constant_of_bounded hD
  refine ⟨K, hK, ?_⟩
  intro p
  have hb := hp _ _ (memH10_coordinates p)
  have hfinite : ENNReal.ofReal K * eLpNorm (gradientMap D p) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)
  have hreal := ENNReal.toReal_mono hfinite hb
  simpa only [Lp.norm_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK.le] using hreal

/-- Coercivity on every bounded-domain graph. -/
theorem energy_coercive_of_bounded {D : Set Plane} (hD : Bornology.IsBounded D) :
    IsCoercive (energy D) := by
  obtain ⟨K, hK, hp⟩ := exists_coordinate_bound_of_bounded hD
  have hden : 0 < K ^ 2 + 1 := by positivity
  refine ⟨1 / (K ^ 2 + 1), div_pos zero_lt_one hden, ?_⟩
  intro p
  rw [energy_apply, real_inner_self_eq_norm_sq]
  have hs : ‖valueMap D p‖ ^ 2 ≤ K ^ 2 * ‖gradientMap D p‖ ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg (valueMap D p))
      (mul_nonneg hK.le (norm_nonneg (gradientMap D p)))).2 (hp p)
    simpa only [mul_pow] using h
  have htotal : ‖p‖ ^ 2 ≤ (K ^ 2 + 1) * ‖gradientMap D p‖ ^ 2 := by
    rw [norm_sq]
    nlinarith
  calc
    1 / (K ^ 2 + 1) * ‖p‖ * ‖p‖ = ‖p‖ ^ 2 / (K ^ 2 + 1) := by ring
    _ ≤ ‖gradientMap D p‖ ^ 2 := (div_le_iff₀ hden).2 (by nlinarith [htotal])

/-- Source integration on a bounded measurable set. -/
def forcingOn (D : Set Plane) (hD : MeasurableSet D) (hb : Bornology.IsBounded D) :
    space D →L[ℝ] ℝ :=
  (innerSL ℝ (indicatorConstLp 2 hD hb.measure_lt_top.ne (1 : ℝ))).comp (valueMap D)

theorem forcingOn_apply (D : Set Plane) (hD : MeasurableSet D) (hb : Bornology.IsBounded D)
    (p : space D) : forcingOn D hD hb p = ∫ x in D, valueMap D p x :=
  L2.inner_indicatorConstLp_one hD hb.measure_lt_top.ne _

/-- Lax--Milgram existence does not require convexity, smoothness, or even
openness: the actual smooth graph closure handles arbitrary measurable sets. -/
theorem exists_variational_solution_of_bounded {D : Set Plane}
    (hD : MeasurableSet D) (hb : Bornology.IsBounded D) :
    ∃ p : space D, ∀ q : space D, energy D p q = forcingOn D hD hb q := by
  let coercive := energy_coercive_of_bounded hb
  let f := (InnerProductSpace.toDual ℝ (space D)).symm (forcingOn D hD hb)
  let p := coercive.continuousLinearEquivOfBilin.symm f
  refine ⟨p, ?_⟩
  intro q
  calc
    energy D p q = inner (𝕜 := ℝ) (coercive.continuousLinearEquivOfBilin p) q :=
      (coercive.continuousLinearEquivOfBilin_apply p q).symm
    _ = inner (𝕜 := ℝ) f q := by rw [ContinuousLinearEquiv.apply_symm_apply]
    _ = forcingOn D hD hb q := InnerProductSpace.toDual_symm_apply

/-- The Hilbert energy is the integral over the original measurable set. -/
theorem energy_eq_setIntegral_of_measurable {D : Set Plane} (hD : MeasurableSet D)
    (p q : space D) : energy D p q =
      ∫ x in D, inner (𝕜 := ℝ) (gradientMap D p x) (gradientMap D q x) := by
  rw [energy_apply, L2.inner_def, ← integral_add_compl hD (L2.integrable_inner _ _)]
  have hzero : (∫ x in Dᶜ, inner (𝕜 := ℝ) (gradientMap D p x) (gradientMap D q x)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [(memH10_coordinates p).gradient_ae_zero_off] with x hx
    simp only [Pi.zero_apply] at hx
    simp [hx]
  rw [hzero, add_zero]

/-- Extraction of the full original weak equation on a bounded measurable
set, against every admissible concrete value/gradient pair. -/
theorem variational_isWeakTorsion_of_bounded {D : Set Plane}
    (hD : MeasurableSet D) (hb : Bornology.IsBounded D) (p : space D)
    (hp : ∀ q : space D, energy D p q = forcingOn D hD hb q) :
    IsWeakTorsion D (valueMap D p) (gradientMap D p) := by
  refine ⟨memH10_coordinates p, ?_⟩
  intro v h hv
  have heq := hp (ofMemH10 hv)
  rw [energy_eq_setIntegral_of_measurable hD, forcingOn_apply,
    valueMap_ofMemH10, gradientMap_ofMemH10] at heq
  calc
    (∫ x in D, inner (𝕜 := ℝ) (gradientMap D p x) (h x)) =
        ∫ x in D, inner (𝕜 := ℝ) (gradientMap D p x) (hv.2.1.toLp h x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hv.2.1.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x in D, hv.1.toLp v x := heq
    _ = ∫ x in D, v x := integral_congr_ae (ae_restrict_of_ae hv.1.coeFn_toLp)

/-- Actual weak-solution existence on every bounded measurable set, including
all the possibly nonconvex marked radial domains of the source. -/
theorem exists_dirichletSolution_of_bounded {D : Set Plane}
    (hD : MeasurableSet D) (hb : Bornology.IsBounded D) : Nonempty (DirichletSolution D) := by
  obtain ⟨p, hp⟩ := exists_variational_solution_of_bounded hD hb
  exact ⟨⟨valueMap D p, gradientMap D p, variational_isWeakTorsion_of_bounded hD hb p hp⟩⟩

/-- A chosen solution for any bounded measurable domain. -/
def solutionOn (D : Set Plane) (hD : MeasurableSet D) (hb : Bornology.IsBounded D) :
    DirichletSolution D := Classical.choice (exists_dirichletSolution_of_bounded hD hb)

end Torsion.HilbertDirichlet

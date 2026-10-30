module

public import Torsion.Definitions
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual compact deformation maps

The maps used in localized shape calculus are the concrete maps
`z ↦ z + t • V z`. A smooth compact vector field is globally Lipschitz;
for sufficiently small parameters the deformation is an actual global
homeomorphism, constructed by the quantitative inverse function theorem.
No injectivity, surjectivity or inverse-map certificate is assumed.
-/

noncomputable section
open Set
open scoped Topology ContDiff NNReal

namespace Torsion.Shape

/-- The concrete one-parameter compact deformation. -/
def deformation (V : Plane → Plane) (t : ℝ) (z : Plane) : Plane := z + t • V z

@[simp] theorem deformation_zero (V : Plane → Plane) : deformation V 0 = id := by
  funext z
  simp [deformation]

theorem deformation_eq_self_of_not_mem_tsupport (V : Plane → Plane) (t : ℝ)
    {z : Plane} (hz : z ∉ tsupport V) : deformation V t z = z := by
  have hV : V z = 0 := by
    by_contra hne
    exact hz (subset_tsupport V hne)
  simp [deformation, hV]

/-- The spatial derivative is exactly `I + t DV`. -/
theorem deformation_hasFDerivAt {V : Plane → Plane} {z : Plane}
    (hV : DifferentiableAt ℝ V z) (t : ℝ) :
    HasFDerivAt (deformation V t)
      (ContinuousLinearMap.id ℝ Plane + t • fderiv ℝ V z) z := by
  convert (hasFDerivAt_id z).add (hV.hasFDerivAt.const_smul t) using 1
  rfl

/-- The parameter derivative is the original physical vector field. -/
theorem deformation_hasDerivAt (V : Plane → Plane) (z : Plane) (t : ℝ) :
    HasDerivAt (fun s : ℝ => deformation V s z) (V z) t := by
  simpa [deformation] using (hasDerivAt_id t).smul_const (V z) |>.const_add z

theorem deformation_contDiff {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (t : ℝ) :
    ContDiff ℝ ∞ (deformation V t) :=
  contDiff_id.add (hV.const_smul t)

/-- The displacement Lipschitz constant gives a quantitative approximation
of the identity on the whole physical plane. -/
theorem deformation_approximatesLinearOn {V : Plane → Plane} {K : ℝ≥0}
    (hV : LipschitzWith K V) (t : ℝ) :
    ApproximatesLinearOn (deformation V t) (ContinuousLinearMap.id ℝ Plane)
      univ (‖t‖₊ * K) := by
  intro x _ y _
  have heq : deformation V t x - deformation V t y -
      (ContinuousLinearMap.id ℝ Plane) (x - y) = t • (V x - V y) := by
    simp only [deformation, ContinuousLinearMap.id_apply, smul_sub]
    abel
  rw [heq, norm_smul]
  change ‖t‖ * ‖V x - V y‖ ≤ (‖t‖ * (K : ℝ)) * ‖x - y‖
  exact (mul_le_mul_of_nonneg_left (hV.norm_sub_le x y) (norm_nonneg t)).trans_eq
    (mul_assoc _ _ _).symm

/-- For a small parameter the concrete map is a global homeomorphism. -/
def deformationHomeomorph {V : Plane → Plane} {K : ℝ≥0}
    (hV : LipschitzWith K V) (t : ℝ) (ht : ‖t‖₊ * K < 1) : Plane ≃ₜ Plane :=
  ApproximatesLinearOn.toHomeomorph (deformation V t)
    (f' := ContinuousLinearEquiv.refl ℝ Plane)
    (deformation_approximatesLinearOn hV t) (Or.inr (by simpa using ht))

@[simp] theorem deformationHomeomorph_apply {V : Plane → Plane} {K : ℝ≥0}
    (hV : LipschitzWith K V) (t : ℝ) (ht : ‖t‖₊ * K < 1) (z : Plane) :
    deformationHomeomorph hV t ht z = deformation V t z := rfl

/-- The inverse has the quantitative Lipschitz bound needed to transport
weak gradients in the opposite direction. -/
theorem deformationHomeomorph_symm_lipschitz {V : Plane → Plane} {K : ℝ≥0}
    (hV : LipschitzWith K V) (t : ℝ) (ht : ‖t‖₊ * K < 1) :
    LipschitzWith ((1 - ‖t‖₊ * K)⁻¹)
      ((deformationHomeomorph hV t ht).symm : Plane → Plane) := by
  have ha := (deformation_approximatesLinearOn hV t).antilipschitz
    (f' := ContinuousLinearEquiv.refl ℝ Plane) (Or.inr (by simpa using ht))
  have hanti : AntilipschitzWith ((1 - ‖t‖₊ * K)⁻¹) (deformation V t) := by
    intro x y
    simpa using ha ⟨x, mem_univ x⟩ ⟨y, mem_univ y⟩
  exact hanti.to_rightInverse (deformationHomeomorph hV t ht).apply_symm_apply

theorem deformation_derivative_norm_lt {V : Plane → Plane} {K : ℝ≥0}
    (hV : LipschitzWith K V) (t : ℝ) (ht : ‖t‖₊ * K < 1) (z : Plane) :
    ‖-(t • fderiv ℝ V z)‖ < 1 := by
  rw [norm_neg, norm_smul]
  have hb : ‖fderiv ℝ V z‖ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz ℝ hV
  have ht' : ‖t‖ * (K : ℝ) < 1 := by exact_mod_cast ht
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg t)).trans_lt ht'

/-- The actual spatial derivative is an invertible continuous linear map;
its inverse is constructed by the convergent Neumann series. -/
def deformationDerivativeEquiv {V : Plane → Plane} {K : ℝ≥0}
    (hV : LipschitzWith K V) (t : ℝ) (ht : ‖t‖₊ * K < 1) (z : Plane) :
    Plane ≃L[ℝ] Plane :=
  ContinuousLinearEquiv.ofUnit (Units.oneSub (-(t • fderiv ℝ V z))
    (deformation_derivative_norm_lt hV t ht z))

@[simp] theorem deformationDerivativeEquiv_coe {V : Plane → Plane} {K : ℝ≥0}
    (hV : LipschitzWith K V) (t : ℝ) (ht : ‖t‖₊ * K < 1) (z : Plane) :
    (deformationDerivativeEquiv hV t ht z : Plane →L[ℝ] Plane) =
      ContinuousLinearMap.id ℝ Plane + t • fderiv ℝ V z := by
  ext w
  change (1 - -(t • fderiv ℝ V z)) w =
    (ContinuousLinearMap.id ℝ Plane + t • fderiv ℝ V z) w
  simp

/-- The actual global inverse is smooth: the compact deformation is a
genuine diffeomorphism, not merely an assumed change of domain labels. -/
theorem deformationHomeomorph_symm_contDiff {V : Plane → Plane} {K : ℝ≥0}
    (hV : ContDiff ℝ ∞ V) (hK : LipschitzWith K V) (t : ℝ) (ht : ‖t‖₊ * K < 1) :
    ContDiff ℝ ∞ ((deformationHomeomorph hK t ht).symm : Plane → Plane) := by
  apply Homeomorph.contDiff_symm (deformationHomeomorph hK t ht)
    (f₀' := fun z => deformationDerivativeEquiv hK t ht z)
  · intro z
    rw [deformationDerivativeEquiv_coe]
    exact deformation_hasFDerivAt ((hV.differentiable (by simp)) z) t
  · exact deformation_contDiff hV t

/-- Compact smooth vector fields have a genuine finite global Lipschitz bound. -/
theorem exists_lipschitz_of_contDiff_compact {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    ∃ K : ℝ≥0, LipschitzWith K V := by
  obtain ⟨C, hC⟩ := (hVc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hV.continuous_fderiv (by simp))
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  refine ⟨K, lipschitzWith_of_nnnorm_fderiv_le (hV.differentiable (by simp)) ?_⟩
  intro z
  change ‖fderiv ℝ V z‖ ≤ max C 0
  exact (hC z).trans (le_max_left _ _)

/-- A uniform parameter interval on which all concrete compact deformations
are global homeomorphisms. The maps equal the identity off the vector field's
support, as proved above. -/
theorem exists_deformationHomeomorph_of_contDiff_compact {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      ∃ e : Plane ≃ₜ Plane, (e : Plane → Plane) = deformation V t := by
  obtain ⟨K, hK⟩ := exists_lipschitz_of_contDiff_compact hV hVc
  refine ⟨1 / ((K : ℝ) + 1), by positivity, ?_⟩
  intro t ht
  have hsmall : ‖t‖₊ * K < 1 := by
    have hmul : |t| * ((K : ℝ) + 1) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < (K : ℝ) + 1)).mp ht
    have hreal : |t| * (K : ℝ) < 1 := by nlinarith [abs_nonneg t]
    exact_mod_cast hreal
  exact ⟨deformationHomeomorph hK t hsmall, rfl⟩

/-- Pullback by a smooth actual homeomorphism preserves the concrete compact
test core on the inverse image domain. This is the core transport needed to
pull deformed weak solutions back to a fixed domain. -/
theorem test_pullback {D : Set Plane} {f : Plane → ℝ} (e : Plane ≃ₜ Plane)
    (he : ContDiff ℝ ∞ (e : Plane → Plane)) (hf : IsTest (e '' D) f) :
    IsTest D (f ∘ e) := by
  refine ⟨hf.1.comp he, hf.2.1.comp_homeomorph e, ?_⟩
  have hsupp : tsupport (f ∘ e) ⊆ e ⁻¹' tsupport f := by
    apply closure_minimal
    · intro z hz
      exact subset_tsupport f hz
    · exact (isClosed_tsupport f).preimage e.continuous
  intro z hz
  obtain ⟨w, hw, hew⟩ := hf.2.2 (hsupp hz)
  exact e.injective hew ▸ hw

/-- In particular the actual compact deformation transports every smooth
test on the physical image back to a test on the fixed domain. -/
theorem test_pullback_deformation {D : Set Plane} {f : Plane → ℝ}
    {V : Plane → Plane} {K : ℝ≥0} (hV : ContDiff ℝ ∞ V)
    (hK : LipschitzWith K V) (t : ℝ) (ht : ‖t‖₊ * K < 1)
    (hf : IsTest (deformation V t '' D) f) :
    IsTest D (fun z => f (deformation V t z)) := by
  exact test_pullback (deformationHomeomorph hK t ht) (deformation_contDiff hV t) hf

/-- Smooth compact tests also push forward to the actual deformed domain. -/
theorem test_pushforward_deformation {D : Set Plane} {f : Plane → ℝ}
    {V : Plane → Plane} {K : ℝ≥0} (hV : ContDiff ℝ ∞ V)
    (hK : LipschitzWith K V) (t : ℝ) (ht : ‖t‖₊ * K < 1)
    (hf : IsTest D f) :
    IsTest (deformation V t '' D)
      (f ∘ (deformationHomeomorph hK t ht).symm) := by
  have hD : (deformationHomeomorph hK t ht).symm '' (deformation V t '' D) = D := by
    change (deformationHomeomorph hK t ht).symm ''
      ((deformationHomeomorph hK t ht) '' D) = D
    exact (deformationHomeomorph hK t ht).symm_image_image D
  exact test_pullback (deformationHomeomorph hK t ht).symm
    (deformationHomeomorph_symm_contDiff hV hK t ht) (hD.symm ▸ hf)

end Torsion.Shape

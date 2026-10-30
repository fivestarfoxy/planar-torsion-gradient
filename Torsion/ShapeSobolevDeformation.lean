import Torsion.ShapeSobolevTransport
import Torsion.ShapeCoefficients

/-!
# Actual compact deformations transport the concrete weak Dirichlet graph

The small parameter interval, global inverse, differential bound and volume
distortion are all proved for the actual map `z ↦ z + t V(z)`.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal ContDiff NNReal

namespace Torsion.Shape

/-- The differential of the actual deformation has its elementary uniform
operator-norm bound, proved from the original displacement Lipschitz bound. -/
theorem deformation_fderiv_norm_le {V : Plane → Plane} {K : ℝ≥0}
    (hV : Differentiable ℝ V) (hK : LipschitzWith K V) (t : ℝ) (z : Plane) :
    ‖fderiv ℝ (deformation V t) z‖ ≤ 1 + |t| * (K : ℝ) := by
  rw [(deformation_hasFDerivAt (hV z) t).fderiv]
  calc
    _ ≤ ‖ContinuousLinearMap.id ℝ Plane‖ + ‖t • fderiv ℝ V z‖ := norm_add_le _ _
    _ = 1 + |t| * ‖fderiv ℝ V z‖ := by rw [ContinuousLinearMap.norm_id, norm_smul, Real.norm_eq_abs]
    _ ≤ _ := add_le_add_left
      (mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hK) (abs_nonneg t)) 1

/-- Actual H¹₀ transport for every smooth compact vector field. In one common
parameter neighborhood the concrete deformed-domain weak graph pulls back
to the fixed domain by the genuine transpose differential. -/
theorem exists_MemH10_pullback_deformation {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      ∃ e : Plane ≃ₜ Plane, (e : Plane → Plane) = deformation V t ∧
        ContDiff ℝ ∞ (e.symm : Plane → Plane) ∧
        ∀ (D : Set Plane) (u : Plane → ℝ) (g : Plane → Plane),
          MemH10 (deformation V t '' D) u g →
          MemH10 D (u ∘ e) (gradientPullback e g) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_of_contDiff_compact hV hVc
  obtain ⟨δJ, hδJ, hJ⟩ := exists_uniform_jacobian_half_le hV hVc
  let δ : ℝ := min (1 / ((K : ℝ) + 1)) δJ
  refine ⟨δ, lt_min (by positivity) hδJ, ?_⟩
  intro t ht
  have htK : ‖t‖₊ * K < 1 := by
    have ht₁ : |t| < 1 / ((K : ℝ) + 1) := ht.trans_le (min_le_left _ _)
    have hmul : |t| * ((K : ℝ) + 1) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < (K : ℝ) + 1)).mp ht₁
    have hreal : |t| * (K : ℝ) < 1 := by nlinarith [abs_nonneg t]
    exact_mod_cast hreal
  let e := deformationHomeomorph hK t htK
  have he : ContDiff ℝ ∞ (e : Plane → Plane) := deformation_contDiff hV t
  have hJac (z : Plane) : (1 / 2 : ℝ) ≤ |(fderiv ℝ (e : Plane → Plane) z).det| := by
    have h := hJ t (ht.trans_le (min_le_right _ _)) z
    exact h.trans (le_abs_self _)
  have hmap : Measure.map e volume ≤ (ENNReal.ofReal (1 / 2 : ℝ))⁻¹ •
      (volume : Measure Plane) :=
    map_volume_le_of_det_lower e (fun z => (he.differentiable (by simp) z).hasFDerivAt)
      (by norm_num) hJac
  refine ⟨e, rfl, deformationHomeomorph_symm_contDiff hV hK t htK, ?_⟩
  intro D u g hu
  exact MemH10_pullback e he
    (ENNReal.inv_ne_top.mpr (by norm_num : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0))
    hmap (deformation_fderiv_norm_le (hV.differentiable (by simp)) hK t) hu

/-- Both directions of the original concrete H¹₀ graph transport hold on a
common parameter neighborhood for every actual smooth compact deformation.
The inverse's volume distortion and derivative bounds are proved as well. -/
theorem exists_MemH10_transport_deformation {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      ∃ e : Plane ≃ₜ Plane, (e : Plane → Plane) = deformation V t ∧
        ContDiff ℝ ∞ (e.symm : Plane → Plane) ∧
        (∀ (D : Set Plane) (u : Plane → ℝ) (g : Plane → Plane),
          MemH10 (deformation V t '' D) u g →
          MemH10 D (u ∘ e) (gradientPullback e g)) ∧
        (∀ (D : Set Plane) (u : Plane → ℝ) (g : Plane → Plane),
          MemH10 D u g → MemH10 (deformation V t '' D)
            (u ∘ e.symm) (gradientPullback e.symm g)) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_of_contDiff_compact hV hVc
  obtain ⟨δJ, hδJ, hJ⟩ := exists_uniform_jacobian_bounds hV hVc
  let δ : ℝ := min (1 / ((K : ℝ) + 1)) δJ
  refine ⟨δ, lt_min (by positivity) hδJ, ?_⟩
  intro t ht
  have htK : ‖t‖₊ * K < 1 := by
    have ht₁ : |t| < 1 / ((K : ℝ) + 1) := ht.trans_le (min_le_left _ _)
    have hmul : |t| * ((K : ℝ) + 1) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < (K : ℝ) + 1)).mp ht₁
    have hreal : |t| * (K : ℝ) < 1 := by nlinarith [abs_nonneg t]
    exact_mod_cast hreal
  let e := deformationHomeomorph hK t htK
  have he : ContDiff ℝ ∞ (e : Plane → Plane) := deformation_contDiff hV t
  have hes : ContDiff ℝ ∞ (e.symm : Plane → Plane) :=
    deformationHomeomorph_symm_contDiff hV hK t htK
  have hJac (z : Plane) : (1 / 2 : ℝ) ≤ (fderiv ℝ (e : Plane → Plane) z).det ∧
      (fderiv ℝ (e : Plane → Plane) z).det ≤ 3 / 2 :=
    hJ t (ht.trans_le (min_le_right _ _)) z
  have hlower (z : Plane) : (1 / 2 : ℝ) ≤ |(fderiv ℝ (e : Plane → Plane) z).det| :=
    (hJac z).1.trans (le_abs_self _)
  have hupper (z : Plane) : |(fderiv ℝ (e : Plane → Plane) z).det| ≤ 3 / 2 := by
    rw [abs_of_nonneg (by linarith [(hJac z).1])]
    exact (hJac z).2
  have hmap : Measure.map e volume ≤ (ENNReal.ofReal (1 / 2 : ℝ))⁻¹ •
      (volume : Measure Plane) :=
    map_volume_le_of_det_lower e (fun z => (he.differentiable (by simp) z).hasFDerivAt)
      (by norm_num) hlower
  have hmaps : Measure.map e.symm volume ≤ ENNReal.ofReal (3 / 2 : ℝ) •
      (volume : Measure Plane) :=
    map_symm_volume_le_of_det_upper e
      (fun z => (he.differentiable (by simp) z).hasFDerivAt) hupper
  refine ⟨e, rfl, hes, ?_, ?_⟩
  · intro D u g hu
    exact MemH10_pullback e he
      (ENNReal.inv_ne_top.mpr (by norm_num : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0))
      hmap (deformation_fderiv_norm_le (hV.differentiable (by simp)) hK t) hu
  · intro D u g hu
    have hDs : e.symm '' (deformation V t '' D) = D := e.symm_image_image D
    apply MemH10_pullback e.symm hes ENNReal.ofReal_ne_top hmaps
      (fun _ => norm_fderiv_le_of_lipschitz ℝ (deformationHomeomorph_symm_lipschitz hK t htK))
    rwa [hDs]

end Torsion.Shape

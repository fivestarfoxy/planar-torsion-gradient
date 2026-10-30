module

public import Torsion.RadialDeformationImage
public import Torsion.RadialFluxConcavity.Transfer

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Constructed localized radial shape deformations

Every compact smooth angular perturbation is realized by a concrete smooth
compact physical vector field supported strictly above the real axis. For
all sufficiently small parameters, the map `id + t V` is an actual smooth
global diffeomorphism and sends the reference radial domain exactly onto
the prescribed perturbed radial domain.
-/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace Torsion.Shape

/-- Actual realization of smooth localized angular profile changes by
compact smooth physical deformations. No reference-boundary smoothness,
geometric mapping assumption or abstract deformation certificate is used. -/
theorem exists_local_radial_deformation {R f : ℝ → ℝ}
    (hR : ContinuousOn R (Icc 0 Real.pi))
    (hRpos : ∀ θ ∈ Icc 0 Real.pi, 0 < R θ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ Ioo 0 Real.pi) :
    ∃ (V : Plane → Plane) (δ : ℝ), ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      tsupport V ⊆ upperHalfPlane ∧ 0 < δ ∧
      (∀ x : ℝ, V =ᶠ[𝓝 (x : Plane)] 0) ∧
      (∀ θ ∈ Ioo 0 Real.pi,
        V ((R θ : Plane) * Complex.exp ((θ : Plane) * Complex.I)) =
          (f θ : ℝ) • Complex.exp ((θ : Plane) * Complex.I)) ∧
      ∀ t : ℝ, |t| < δ →
        (fun θ => R θ + t * f θ) ∈ RadialFluxConcavity.positiveContinuousProfiles ∧
        ∃ e : Plane ≃ₜ Plane,
          (e : Plane → Plane) = deformation V t ∧
          ContDiff ℝ ∞ (e : Plane → Plane) ∧
          ContDiff ℝ ∞ (e.symm : Plane → Plane) ∧
          e '' radialDomain R = radialDomain (fun θ => R θ + t * f θ) := by
  obtain ⟨β, m, M, hβ, hβc, hm, hmM, hβsupp, hβzero, hβR⟩ := exists_radialCollar hR hRpos
  let V := radialDisplacement β f
  have hV := radialDisplacement_contDiff (half_pos hm) hβ hβsupp hf hfc hfU
  have hVc := (radialDisplacement_compact_upper (half_pos hm) hβsupp hfc hfU).1
  have hVU := (radialDisplacement_compact_upper (half_pos hm) hβsupp hfc hfU).2
  obtain ⟨Kβ, hKβ⟩ := exists_lipschitz_scalar_of_contDiff_compact hβ hβc
  obtain ⟨KV, hKV⟩ := exists_lipschitz_of_contDiff_compact hV hVc
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hf.continuous
  let B : ℝ := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hfB (θ : ℝ) : |f θ| ≤ B := by
    rw [← Real.norm_eq_abs]
    exact (hC θ).trans (by dsimp [B]; linarith [le_max_left C 0])
  let δ : ℝ := 1 / ((Kβ : ℝ) * B + (KV : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨V, δ, hV, hVc, hVU, hδ, ?_, ?_, ?_⟩
  · intro x
    exact radialDisplacement_eventually_zero_at_real (half_pos hm) hβsupp hfc hfU x
  · intro θ hθ
    dsimp only [V]
    rw [radialDisplacement_polar (hRpos θ (Ioo_subset_Icc_self hθ)) hθ,
      hβR θ (Ioo_subset_Icc_self hθ), one_mul]
  · intro t ht
    have hmul : |t| * ((Kβ : ℝ) * B + (KV : ℝ) + 1) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < (Kβ : ℝ) * B + (KV : ℝ) + 1)).mp ht
    have htβ : |t| * ((Kβ : ℝ) * B) < 1 := by
      nlinarith [abs_nonneg t, KV.coe_nonneg]
    have htV : ‖t‖₊ * KV < 1 := by
      have hreal : |t| * (KV : ℝ) < 1 := by
        nlinarith [abs_nonneg t, mul_nonneg Kβ.coe_nonneg hB.le]
      exact_mod_cast hreal
    have htθ (θ : ℝ) : |t * f θ| * (Kβ : ℝ) < 1 := by
      rw [abs_mul]
      calc
        _ ≤ (|t| * B) * (Kβ : ℝ) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hfB θ) (abs_nonneg t)) Kβ.coe_nonneg
        _ = |t| * ((Kβ : ℝ) * B) := by ring
        _ < 1 := htβ
    have hpert : (fun θ => R θ + t * f θ) ∈ RadialFluxConcavity.positiveContinuousProfiles := by
      refine ⟨hR.add (continuousOn_const.mul hf.continuous.continuousOn), ?_⟩
      intro θ hθ
      have hmono := perturbedRadius_strictMono hKβ (htθ θ)
      have hpos := hmono (hRpos θ hθ)
      simpa only [perturbedRadius, hβzero, hβR θ hθ, mul_zero, add_zero, mul_one] using hpos
    refine ⟨hpert, deformationHomeomorph hKV t htV, rfl,
      deformation_contDiff hV t, deformationHomeomorph_symm_contDiff hV hKV t htV, ?_⟩
    exact deformation_radialDomain_eq (fun θ hθ => hRpos θ (Ioo_subset_Icc_self hθ))
      hKβ hβzero (fun θ hθ => hβR θ (Ioo_subset_Icc_self hθ)) t (fun θ _ => htθ θ)

end Torsion.Shape

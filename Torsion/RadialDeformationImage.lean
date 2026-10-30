module

public import Torsion.RadialDeformationField
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Exact physical realization of radial profile perturbations

The concrete compact radial vector field moves each radius by
`r ↦ r + t β(r) f(θ)`. A quantitative Lipschitz estimate makes this map
strictly increasing. The intermediate value theorem then identifies the
actual image of the original radial domain with the prescribed perturbed
radial domain, including both inclusion directions.
-/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace Torsion.Shape

def perturbedRadius (β : ℝ → ℝ) (A r : ℝ) : ℝ := r + A * β r

theorem perturbedRadius_strictMono {β : ℝ → ℝ} {K : ℝ≥0}
    (hβ : LipschitzWith K β) {A : ℝ} (hA : |A| * (K : ℝ) < 1) :
    StrictMono (perturbedRadius β A) := by
  intro x y hxy
  have hd : |β y - β x| ≤ (K : ℝ) * (y - x) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hxy)] using hβ.norm_sub_le y x
  have hmul : |A * (β y - β x)| ≤ (|A| * (K : ℝ)) * (y - x) := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hd (abs_nonneg A)).trans_eq (mul_assoc _ _ _).symm
  have hlo := (abs_le.mp hmul).1
  have hp := mul_pos (sub_pos.mpr hA) (sub_pos.mpr hxy)
  dsimp [perturbedRadius]
  nlinarith

theorem deformation_radialDisplacement_polar {β f : ℝ → ℝ} {r θ : ℝ}
    (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi) (t : ℝ) :
    deformation (radialDisplacement β f) t
      ((r : Plane) * Complex.exp ((θ : Plane) * Complex.I)) =
    ((perturbedRadius β (t * f θ) r : ℝ) : Plane) *
      Complex.exp ((θ : Plane) * Complex.I) := by
  rw [deformation, radialDisplacement_polar hr hθ]
  simp only [smul_smul, perturbedRadius, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.real_smul]
  ring

/-- The actual compact radial displacement maps the actual original radial
domain exactly to the requested perturbed profile. The scalar cutoff is
one at the reference boundary, not silently replaced by a domain label. -/
theorem deformation_radialDomain_eq {R β f : ℝ → ℝ} {K : ℝ≥0}
    (hR : ∀ θ ∈ Ioo 0 Real.pi, 0 < R θ)
    (hβ : LipschitzWith K β) (hβzero : β 0 = 0)
    (hβR : ∀ θ ∈ Ioo 0 Real.pi, β (R θ) = 1)
    (t : ℝ) (ht : ∀ θ ∈ Ioo 0 Real.pi, |t * f θ| * (K : ℝ) < 1) :
    deformation (radialDisplacement β f) t '' radialDomain R =
      radialDomain (fun θ => R θ + t * f θ) := by
  apply Subset.antisymm
  · rintro w ⟨z, ⟨θ, r, hθ, hθπ, hr, hrR, rfl⟩, rfl⟩
    have hθU : θ ∈ Ioo 0 Real.pi := ⟨hθ, hθπ⟩
    have hmono := perturbedRadius_strictMono hβ (ht θ hθU)
    have hq0 : perturbedRadius β (t * f θ) 0 = 0 := by simp [perturbedRadius, hβzero]
    have hqR : perturbedRadius β (t * f θ) (R θ) = R θ + t * f θ := by
      simp [perturbedRadius, hβR θ hθU]
    refine ⟨θ, perturbedRadius β (t * f θ) r, hθ, hθπ, ?_, ?_, ?_⟩
    · simpa only [hq0] using hmono hr
    · simpa only [hqR] using hmono hrR
    · exact deformation_radialDisplacement_polar hr hθU t
  · rintro w ⟨θ, ρ, hθ, hθπ, hρ, hρR, rfl⟩
    change ρ < R θ + t * f θ at hρR
    have hθU : θ ∈ Ioo 0 Real.pi := ⟨hθ, hθπ⟩
    have hRpos := hR θ hθU
    have hq0 : perturbedRadius β (t * f θ) 0 = 0 := by simp [perturbedRadius, hβzero]
    have hqR : perturbedRadius β (t * f θ) (R θ) = R θ + t * f θ := by
      simp [perturbedRadius, hβR θ hθU]
    have hqcont : Continuous (perturbedRadius β (t * f θ)) :=
      continuous_id.add (continuous_const.mul hβ.continuous)
    have hρmem : ρ ∈ Icc (perturbedRadius β (t * f θ) 0)
        (perturbedRadius β (t * f θ) (R θ)) := by
      rw [hq0, hqR]
      exact ⟨hρ.le, hρR.le⟩
    obtain ⟨r, hrcc, hreq⟩ := intermediate_value_Icc hRpos.le hqcont.continuousOn hρmem
    have hr : 0 < r := by
      apply lt_of_le_of_ne hrcc.1
      intro h0
      have he := hreq
      rw [← h0, hq0] at he
      linarith
    have hrR : r < R θ := by
      apply lt_of_le_of_ne hrcc.2
      intro heq
      have he := hreq
      rw [heq, hqR] at he
      linarith
    refine ⟨(r : Plane) * Complex.exp ((θ : Plane) * Complex.I),
      ⟨θ, r, hθ, hθπ, hr, hrR, rfl⟩, ?_⟩
    rw [deformation_radialDisplacement_polar hr hθU t, hreq]

end Torsion.Shape

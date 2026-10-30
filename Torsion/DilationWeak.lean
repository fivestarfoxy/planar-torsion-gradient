module

public import Torsion.DilationSobolev
public import Torsion.Sobolev
public import Torsion.Main

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Scaling of actual weak torsion solutions

The variational equation is transported through a physical dilation using
scaled H¹₀ tests and the Lebesgue change-of-variables formula. Gradient
uniqueness then turns this construction into the PDE scaling law for every
supplied Dirichlet theory.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Pointwise Topology ENNReal

namespace Torsion

/-- Pulling a test on `sD` back to `D` gives the usual chain-rule gradient. -/
theorem MemH10.pullback_dilate {D : Set ℂ} {v : ℂ → ℝ} {h : ℂ → ℂ}
    (s : ℝ) (hs : 0 < s) (hv : MemH10 (s • D) v h) :
    MemH10 D (fun x => v (s • x)) (fun x => s • h (s • x)) := by
  have hback := (hv.dilate s⁻¹ (inv_pos.2 hs)).const_smul (s ^ 2)
  have hD : s⁻¹ • (s • D) = D := by
    rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  have hvback : (fun x : ℂ => s ^ 2 • scaledValue s⁻¹ v x) =
      (fun x => v (s • x)) := by
    funext x
    simp only [scaledValue, inv_inv, smul_eq_mul, inv_pow]
    field_simp [hs.ne']
  have hhback : (fun x : ℂ => s ^ 2 • scaledGradient s⁻¹ h x) =
      (fun x => s • h (s • x)) := by
    funext x
    simp only [scaledGradient, inv_inv, smul_smul]
    congr 1
    field_simp [hs.ne']
  rw [hD, hvback, hhback] at hback
  exact hback

/-- Torsion scaling is a theorem of the weak equation and H¹₀ approximation. -/
theorem IsWeakTorsion.dilate {D : Set ℂ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsWeakTorsion D u g) (s : ℝ) (hs : 0 < s) :
    IsWeakTorsion (s • D) (scaledValue s u) (scaledGradient s g) := by
  refine ⟨hu.1.dilate s hs, ?_⟩
  intro v h hv
  have htest := hv.pullback_dilate s hs
  have heq := hu.2 (fun x => v (s • x)) (fun x => s • h (s • x)) htest
  calc
    (∫ z in s • D, inner (𝕜 := ℝ) (scaledGradient s g z) (h z)) =
        s ^ 2 * ∫ x in D, inner (𝕜 := ℝ) (s • g x) (h (s • x)) := by
      rw [integral_dilate s hs.ne']
      simp only [scaledGradient, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    _ = s ^ 2 * ∫ x in D, inner (𝕜 := ℝ) (g x) (s • h (s • x)) := by
      simp only [real_inner_smul_left, real_inner_smul_right]
    _ = s ^ 2 * ∫ x in D, v (s • x) := by rw [heq]
    _ = ∫ z in s • D, v z := (integral_dilate s hs.ne' v D).symm

/-- The essential torsion-gradient norm scales under actual physical dilation. -/
theorem DirichletTheory.G_dilate (T : DirichletTheory) (D : ConvexDomain)
    (s : ℝ) (hs : 0 < s) :
    T.G (D.dilate s hs) = ENNReal.ofReal s * T.G D := by
  have hscaled := (T.solution D).weakEquation.dilate s hs
  have hsame := (T.solution (D.dilate s hs)).weakEquation.gradient_ae_eq hscaled
  unfold DirichletTheory.G
  rw [eLpNorm_congr_ae hsame]
  exact eLpNorm_top_scaledGradient s hs (T.solution D).weakGradient D.carrier

/-- A constructed scaling law: geometry, area, and PDE parts are all proved. -/
def ScalingLaw.proved (T : DirichletTheory) : ScalingLaw T where
  domain := fun s hs D => D.dilate s hs
  carrier_eq := fun s hs D => D.dilate_carrier s hs
  area_eq := fun s hs D => D.dilate_area s hs
  gradient_eq := fun s hs D => T.G_dilate D s hs

end Torsion
end

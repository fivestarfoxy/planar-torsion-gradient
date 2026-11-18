module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic

/-! # The classical Poisson equation for the exterior-source trial field -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open InnerProductSpace
open scoped Laplacian Topology

namespace Torsion.Galerkin

private theorem laplacian_shifted_norm_sq (c w : ℂ) :
    Δ (fun z : ℂ => ‖z-c‖ ^ 2) w = 4 := by
  have hg : fderiv ℝ (fun z : ℂ => ‖z-c‖ ^ 2) =
      fun z => 2 • innerSL ℝ (z-c) := by
    funext z
    rw [fderiv_comp_sub (f := fun z : ℂ => ‖z‖^2), fderiv_norm_sq_apply]
  have hh : fderiv ℝ (fun z : ℂ => 2 • innerSL ℝ (z-c)) w = 2 • innerSL ℝ := by
    rw [fderiv_comp_sub (f := fun z : ℂ => 2 • innerSL ℝ z)]
    exact (((innerSL ℝ (E := ℂ)).hasFDerivAt).const_smul (2:ℕ)).fderiv
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, hg, hh]
  norm_num
  change 2 * inner ℝ (1:ℂ) 1 + 2 * inner ℝ Complex.I Complex.I = 4
  norm_num [real_inner_self_eq_norm_sq]

/-- The polynomial particular solution and any finite collection of exterior
logarithmic sources have exactly the required load at every non-source point.
No fit quality or numerical boundary condition is assumed. -/
theorem poissonTrial {ι : Type*} (s : Finset ι) (c : ℂ) (b₀ : ℝ) (b : ι → ℝ)
    (source : ι → ℂ) (w : ℂ) (hs : ∀ i ∈ s, w ≠ source i) :
    Δ ((fun z : ℂ => -(‖z-c‖^2)/4 + (b₀ + ∑ i ∈ s, b i * Real.log ‖z-source i‖)) : ℂ → ℝ) w = -1 := by
  let Q : ℂ → ℝ := fun z => ‖z-c‖^2
  let H (i : ι) : ℂ → ℝ := fun z => b i * Real.log ‖z-source i‖
  have hQ : ContDiffAt ℝ 2 Q w := (show ContDiffAt ℝ 2 (fun z : ℂ => z-c) w by fun_prop).norm_sq (𝕜 := ℝ)
  have hH (i : ι) (h : w ≠ source i) : HarmonicAt (H i) w :=
    (show HarmonicAt (fun z : ℂ => Real.log ‖z-source i‖) w from
      (show AnalyticAt ℂ (fun z : ℂ => z-source i) w by fun_prop).harmonicAt_log_norm
        (sub_ne_zero.mpr h)).const_smul (c := b i)
  have hsum (t : Finset ι) (ht : ∀ i ∈ t, w ≠ source i) : HarmonicAt (∑ i ∈ t, H i) w := by
    classical
    induction t using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact harmonicAt_const 0
    | @insert i t hit ih =>
      rw [Finset.sum_insert hit]
      exact (hH i (ht i (by simp))).add (ih (fun j hj => ht j (by simp [hj])))
  let R : ℂ → ℝ := (fun _ => b₀) + ∑ i ∈ s, H i
  have hR : HarmonicAt R w := (harmonicAt_const b₀).add (hsum s hs)
  have hfun : (fun z : ℂ => -(‖z-c‖^2)/4 + (b₀ + ∑ i ∈ s, b i * Real.log ‖z-source i‖)) =
      (-(1/4) : ℝ) • Q + R := by
    ext z
    simp [Q,R,H, Finset.sum_apply]
    ring
  have hscaled : ContDiffAt ℝ 2 ((-(1/4):ℝ) • Q) w := by
    simpa only [Pi.smul_def] using hQ.const_smul (-(1/4):ℝ)
  rw [hfun, hscaled.laplacian_add hR.1, laplacian_smul _ hQ, hR.2.self_of_nhds]
  change (-(1/4):ℝ) * Δ (fun z : ℂ => ‖z-c‖^2) w + 0 = -1
  rw [laplacian_shifted_norm_sq]
  norm_num

end Torsion.Galerkin

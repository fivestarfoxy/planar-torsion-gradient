module

public import Torsion.WeakHarmonicRegularity
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-! # Interior contraction of the Dirichlet solution

Contracting the independent variable toward an interior point carries the
closed convex body into its interior. This produces harmonic test functions
on open neighborhoods of the whole closed body and approximates its boundary
data uniformly. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion.HermiteHadamard
open WeakHarmonicRegularity

private theorem fderiv_affine_rescale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (a : Plane) (s : ℝ) (z : Plane) :
    fderiv ℝ (fun w => f (a + s • w)) z = s • fderiv ℝ f (a + s • z) := by
  have h := fderiv_comp_smul (f := fun w : Plane => f (a + w)) (x := z) s
  simpa only [fderiv_comp_add_left] using h

/-- The classical planar Laplacian transforms quadratically under a translation
and a positive homothety of the independent variable. -/
theorem planarLaplacian_affine_rescale (f : Plane → ℝ) (a : Plane) {s : ℝ} (hs : 0 < s) (z : Plane) :
    planarLaplacian (fun w => f (a + s • w)) z = s ^ 2 * planarLaplacian f (a + s • z) := by
  let _ : Invertible s := invertibleOfNonzero hs.ne'
  have hg : gradient (fun w => f (a + s • w)) = s • (fun w => gradient f (a + s • w)) := by
    ext w : 1
    simp only [gradient, fderiv_affine_rescale, map_smul, Pi.smul_apply]
  rw [planarLaplacian, planarDivergence, hg, fderiv_const_smul_of_invertible s,
    fderiv_affine_rescale]
  simp only [planarLaplacian, planarDivergence, smul_apply, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

/-- Uniform approximation on the *entire* closed convex body by functions
smooth and harmonic on an open neighborhood of it. -/
theorem exists_neighborhood_harmonic_approximation (D : ConvexDomain)
    {H : Plane → ℝ} (hc : Continuous H) (hs : ContDiffOn ℝ ∞ H D.carrier)
    (hh : ∀ x ∈ D.carrier, planarLaplacian H x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : Plane → ℝ) (N : Set Plane), IsOpen N ∧ closure D.carrier ⊆ N ∧
      Continuous f ∧ ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ N, planarLaplacian f x = 0) ∧
      ∀ x ∈ closure D.carrier, |f x - H x| < ε := by
  obtain ⟨c, hcD⟩ := D.nonempty
  obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuousOn_iff.mp
    (D.bounded.isCompact_closure.uniformContinuousOn_of_continuous hc.continuousOn) ε hε
  let M := Metric.diam (closure D.carrier) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let t := min (1 / 2) (δ / (2 * M))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hδ (by positivity))
  have ht1 : t < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have htM : t * M < δ := by
    have hle : t ≤ δ / (2 * M) := min_le_right _ _
    have := (le_div_iff₀ (by positivity : 0 < 2 * M)).mp hle
    nlinarith
  let A := fun x : Plane => t • c + (1 - t) • x
  have hA : ContDiff ℝ ∞ A := by
    dsimp [A]
    fun_prop
  have hAD : MapsTo A (closure D.carrier) D.carrier := by
    intro x hx
    have hmem : A x ∈ openSegment ℝ c x := ⟨t, 1 - t, ht, sub_pos.mpr ht1, by ring, rfl⟩
    exact interior_subset (D.convex.openSegment_interior_closure_subset_interior
      (D.isOpen.interior_eq.symm ▸ hcD) hx hmem)
  let N := A ⁻¹' D.carrier
  refine ⟨fun x => H (A x), N, D.isOpen.preimage hA.continuous, hAD, hc.comp hA.continuous,
    hs.comp hA.contDiffOn (fun _ h => h), ?_, ?_⟩
  · intro x hx
    rw [show planarLaplacian (fun x => H (A x)) x =
        (1 - t) ^ 2 * planarLaplacian H (A x) from
      planarLaplacian_affine_rescale H _ (sub_pos.mpr ht1) x, hh _ hx, mul_zero]
  · intro x hx
    change |H (A x) - H x| < ε
    rw [← Real.dist_eq]
    apply hcont (A x) (subset_closure (hAD hx)) x hx
    have hd := Metric.dist_le_diam_of_mem D.bounded.closure (subset_closure hcD) hx
    have heq : A x - x = t • (c - x) := by
      change t • c + (1 - t) • x - x = t • (c - x)
      rw [sub_smul, one_smul, smul_sub]
      abel
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht, ← dist_eq_norm]
    exact (mul_le_mul_of_nonneg_left (hd.trans (by dsimp [M]; linarith)) ht.le).trans_lt htM

end Torsion.HermiteHadamard

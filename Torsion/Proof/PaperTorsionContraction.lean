module

public import Torsion.Proof.PaperHarmonicApproximation
public import Torsion.Proof.PaperWeakPoisson
public import Torsion.Proof.PaperBoundaryQuotients

@[expose] public section

/-! # Smooth approximations to torsion on a closed convex body -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace Torsion

/-- Contracting the argument into the interior gives globally smooth test
functions with controlled Laplacian, gradient and boundary values. This
requires no differentiability of the torsion solution on the frontier. -/
theorem DirichletTheory.exists_contracted_torsion (T : DirichletTheory) (D : ConvexDomain)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ u : Plane → ℝ, ContDiff ℝ ∞ u ∧
      (∀ z ∈ D.carrier, WeakHarmonicRegularity.planarLaplacian u z = -(s ^ 2)) ∧
      (∀ z ∈ closure D.carrier, 0 ≤ u z ∧ ‖gradient u z‖ ≤ (T.G D).toReal) ∧
      ∀ z ∈ frontier D.carrier,
        u z ≤ (1-s) * ((T.G D).toReal * diam (closure D.carrier)) := by
  obtain ⟨U, hc, hu, hz, hp, _, hg, hL, _⟩ := T.exists_near_maximal_normal_quotients D
  obtain ⟨c, hcin⟩ := D.nonempty
  let A := fun z : Plane => (1-s) • c + s • z
  have hA : ContDiff ℝ ∞ A := by dsimp [A]; fun_prop
  have hm : MapsTo A (closure D.carrier) D.carrier := by
    intro z hzin
    have ht : A z ∈ openSegment ℝ c z := ⟨1-s, s, sub_pos.mpr hs1, hs, by ring, rfl⟩
    exact interior_subset (D.convex.openSegment_interior_closure_subset_interior
      (D.isOpen.interior_eq.symm ▸ hcin) hzin ht)
  let N := A ⁻¹' D.carrier
  have hN : IsOpen N := D.isOpen.preimage hA.continuous
  have huN : ContDiffOn ℝ ∞ (U ∘ A) N := hu.comp hA.contDiffOn fun _ h => h
  obtain ⟨u,W,htest,hW,hKW,hWN,he⟩ := HermiteHadamard.exists_test_agree_near_compact
    D.bounded.isCompact_closure hN hm huN
  have hlocal (z : Plane) (hzin : z ∈ closure D.carrier) : u =ᶠ[𝓝 z] U ∘ A :=
    Filter.mem_of_superset (hW.mem_nhds (hKW hzin)) fun _ hw => he hw
  have hΔ := (T.solution D).weakEquation.planarLaplacian_representative D.isOpen hu hg
  have hAL : LipschitzWith 1 A := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [A, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hs,
      NNReal.coe_one, one_mul]
    exact mul_le_of_le_one_left dist_nonneg hs1.le
  have hUL : LipschitzWith (T.G D).toNNReal (U ∘ A) := by simpa only [mul_one] using hL.comp hAL
  refine ⟨u, htest.1, ?_, ?_, ?_⟩
  · intro z hzin
    have heq := hlocal z (subset_closure hzin)
    unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
    rw [heq.gradient.fderiv_eq]
    change WeakHarmonicRegularity.planarLaplacian (fun w => U ((1-s) • c + s • w)) z = _
    rw [HermiteHadamard.planarLaplacian_affine_rescale U _ hs z, hΔ _ (hm (subset_closure hzin)), mul_neg_one]
  · intro z hzin
    have heq := hlocal z hzin
    refine ⟨heq.self_of_nhds ▸ hp (A z), ?_⟩
    rw [heq.gradient_eq, gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hUL
  · intro z hf
    have hcl := frontier_subset_closure hf
    rw [(hlocal z hcl).self_of_nhds]
    have hb := hL.dist_le_mul (A z) z
    rw [Real.dist_eq, hz z ((D.isOpen.frontier_eq ▸ hf).2), sub_zero, abs_of_nonneg (hp _),
      dist_eq_norm, show A z - z = (1-s) • (c-z) by
        change (1-s) • c + s • z - z = (1-s) • (c-z)
        rw [smul_sub,sub_smul,sub_smul,one_smul,one_smul]; abel,
      norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hs1), ← dist_eq_norm] at hb
    have hd := Metric.dist_le_diam_of_mem D.bounded.closure (subset_closure hcin) hcl
    calc
      U (A z) ≤ (T.G D).toReal * ((1-s) * dist c z) := hb
      _ ≤ _ := by
        rw [mul_left_comm]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hd ENNReal.toReal_nonneg) (sub_nonneg.mpr hs1.le)

end Torsion

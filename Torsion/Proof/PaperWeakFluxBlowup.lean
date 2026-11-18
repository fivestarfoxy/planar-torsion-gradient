module

public import Torsion.Proof.PaperWeakFluxVolume
public import Torsion.Proof.PaperHarmonicRescaling
public import Torsion.Dilation

@[expose] public section

/-! # The weak torsion flux of contracting boundary bumps -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Pointwise
namespace Torsion.HermiteHadamard
open WeakHarmonicRegularity

/-- A fixed smooth profile centered at `p` at physical scale `ε`. -/
def boundaryBump (b : Plane → ℝ) (p : Plane) (ε : ℝ) (x : Plane) : ℝ := b (ε⁻¹ • (x - p))

theorem boundaryBump_isTest {b : Plane → ℝ} (hb : IsTest univ b) (p : Plane) {ε : ℝ} (hε : 0 < ε) :
    IsTest univ (boundaryBump b p ε) :=
  ⟨hb.1.comp ((contDiff_id.sub contDiff_const).const_smul ε⁻¹),
    (hb.2.1.comp_smul (inv_ne_zero hε.ne')).comp_homeomorph (Homeomorph.subRight p), subset_univ _⟩

private theorem boundaryBump_at_scale (b : Plane → ℝ) (p : Plane) {ε : ℝ} (hε : 0 < ε) (z : Plane) :
    boundaryBump b p ε (p + ε • z) = b z := by
  simp [boundaryBump, hε.ne']

private theorem boundaryBump_laplacian (b : Plane → ℝ) (p : Plane) {ε : ℝ} (hε : 0 < ε) (z : Plane) :
    planarLaplacian (boundaryBump b p ε) (p + ε • z) = ε⁻¹ ^ 2 * planarLaplacian b z := by
  have heq : boundaryBump b p ε = fun w => b (-(ε⁻¹ • p) + ε⁻¹ • w) := by
    funext w
    unfold boundaryBump
    rw [smul_sub, sub_eq_neg_add]
  rw [heq, planarLaplacian_affine_rescale b _ (inv_pos.mpr hε)]
  simp [smul_add, hε.ne']

private theorem integral_physical_rescale (f : Plane → ℝ) (p : Plane) {ε : ℝ} (hε : 0 < ε) :
    (∫ x, f x) = ε ^ 2 * ∫ z, f (p + ε • z) := by
  calc
    _ = ∫ w : Plane, f (p + w) := (integral_add_left_eq_self f p).symm
    _ = _ := by simpa only [smul_set_univ₀ hε.ne', setIntegral_univ] using
        integral_dilate ε hε.ne' (fun w => f (p + w)) univ

private theorem bump_volume_bound (D : ConvexDomain) {b : Plane → ℝ} (hb : IsTest univ b)
    (p : Plane) {ε : ℝ} (hε : 0 < ε) :
    |∫ z in D.carrier, boundaryBump b p ε z| ≤ ε ^ 2 * ∫ z, |b z| := by
  let f := boundaryBump b p ε
  have hf := boundaryBump_isTest hb p hε
  have hi : Integrable f volume := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
  calc
    _ ≤ ∫ z in D.carrier, |f z| := by simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm f (μ := volume.restrict D.carrier))
    _ ≤ ∫ z, |f z| := setIntegral_le_integral hi.abs (ae_of_all _ fun _ => abs_nonneg _)
    _ = _ := by
      rw [integral_physical_rescale (fun z => |f z|) p hε]
      simp only [f, boundaryBump_at_scale b p hε]

private theorem normalized_flux_decomposition (D : ConvexDomain) {u b : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D.carrier u g) (hb : IsTest univ b) (p : Plane) {ε : ℝ} (hε : 0 < ε) :
    weakBoundaryFlux D g (boundaryBump b p ε) / ε =
      (∫ z in D.carrier, boundaryBump b p ε z) / ε +
        ∫ z, (u (p + ε • z) / ε) * planarLaplacian b z := by
  rw [weakBoundaryFlux_eq_volume D hu (boundaryBump_isTest hb p hε), add_div]
  congr 1
  rw [integral_physical_rescale (fun z => u z * planarLaplacian (boundaryBump b p ε) z) p hε]
  simp only [boundaryBump_laplacian b p hε]
  calc
    _ = (ε ^ 2 / ε) * ∫ z, u (p + ε • z) * (ε⁻¹ ^ 2 * planarLaplacian b z) := by ring
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae (Eventually.of_forall ?_)
      intro z
      field_simp

/-- Full one-sided scaling limit. The area term is of order `ε²`, and the
second term converges by the global Lipschitz bound and compact support of the test. -/
theorem weakBoundaryFlux_bump_tendsto (D : ConvexDomain) {u b : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D.carrier u g) (hc : Continuous u) (hb : IsTest univ b) (p n : Plane) (G : ℝ)
    (hlim : ∀ z : Plane, Tendsto (fun ε : ℝ => u (p + ε • z) / ε) (𝓝[>] 0)
      (𝓝 (G * max 0 (inner (𝕜 := ℝ) n z))))
    (hbound : ∀ z : Plane, ∀ {ε : ℝ}, 0 < ε → |u (p + ε • z) / ε| ≤ G * ‖z‖) :
    Tendsto (fun ε : ℝ => weakBoundaryFlux D g (boundaryBump b p ε) / ε) (𝓝[>] 0)
      (𝓝 (∫ z : Plane, G * max 0 (inner (𝕜 := ℝ) n z) * planarLaplacian b z)) := by
  have hsmall : Tendsto (fun ε : ℝ => (∫ z in D.carrier, boundaryBump b p ε z) / ε) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun ε : ℝ => ε * ∫ z, |b z|) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      simpa only [zero_mul] using (h0.mul_const (∫ z, |b z|))
    apply squeeze_zero_norm' _ ht
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have he : 0 < ε := hε
    rw [Real.norm_eq_abs, abs_div, abs_of_pos he, div_le_iff₀ he]
    exact (bump_volume_bound D hb p he).trans_eq (by ring)
  let L := planarLaplacian b
  have hLc : Continuous L := continuous_planarLaplacian_of_contDiff hb.1
  have hLK := compactSupport_planarLaplacian hb.2.1
  have hdom : Integrable (fun z : Plane => G * ‖z‖ * |L z|) volume :=
    ((continuous_const.mul continuous_norm).mul hLc.abs).integrable_of_hasCompactSupport
      ((hLK.norm).mul_left)
  have hmeas (ε : ℝ) : AEStronglyMeasurable (fun z : Plane => (u (p + ε • z) / ε) * L z) volume :=
    (((hc.comp (continuous_const.add (continuous_const_smul ε))).div_const ε).mul hLc).aestronglyMeasurable
  have hdom' : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ z : Plane,
      ‖(u (p + ε • z) / ε) * L z‖ ≤ G * ‖z‖ * |L z| := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply Eventually.of_forall
    intro z
    simpa only [Real.norm_eq_abs, abs_mul] using mul_le_mul_of_nonneg_right (hbound z hε) (abs_nonneg (L z))
  have hconv := tendsto_integral_filter_of_dominated_convergence (fun z : Plane => G * ‖z‖ * |L z|)
    (Eventually.of_forall hmeas) hdom' hdom (Eventually.of_forall fun z => (hlim z).mul_const (L z))
  simpa only [zero_add] using (hsmall.add hconv).congr' (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (normalized_flux_decomposition D hu hb p hε).symm)

end Torsion.HermiteHadamard

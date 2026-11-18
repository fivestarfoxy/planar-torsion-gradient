module

public import Torsion.Proof.PaperMarkedPlacement
public import Torsion.Proof.PaperFlatPatchRadius
public import Torsion.Proof.PaperBoundaryAttainment

@[expose] public section

/-! # The quantitative boundary segment at every maximizing supporting frame -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Pointwise

namespace Torsion.Spectral

private theorem scaled_flat_patch (D : ConvexDomain) {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D.carrier u g) (hc : Continuous u)
    (hzero : (0 : Plane) ∈ closure D.carrier) (hhalf : D.carrier ⊆ upperHalfPlane)
    (hline : ∀ᶠ t : ℝ in 𝓝[>] 0, (t : Plane) * Complex.I ∈ D.carrier)
    (hq : HasMarkedFlux u (spectralConstant secondEigenvalue secondEigenfunction * √D.area))
    {x : ℝ} (hx : |x| ≤ spectralConstant secondEigenvalue secondEigenfunction * √D.area / Real.pi) :
    (x : Plane) ∈ frontier D.carrier := by
  let C := spectralConstant secondEigenvalue secondEigenfunction
  let r := √D.area
  have ha : 0 < D.area := ENNReal.toReal_pos (D.isOpen.measure_ne_zero volume D.nonempty)
    D.bounded.measure_lt_top.ne
  have hr : 0 < r := Real.sqrt_pos.mpr ha
  let s := r⁻¹
  have hs : 0 < s := inv_pos.mpr hr
  let E := D.dilate s hs
  let e : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero s hs.ne'
  have hE : E.carrier = e '' D.carrier := rfl
  have hA : E.area = 1 := by
    rw [ConvexDomain.dilate_area]
    change (√D.area)⁻¹ ^ 2 * D.area = 1
    rw [inv_pow, Real.sq_sqrt ha.le, inv_mul_cancel₀ ha.ne']
  have hEy : (0 : Plane) ∈ closure E.carrier := by
    rw [hE, ← e.image_closure]
    exact ⟨0, hzero, smul_zero s⟩
  have hEh : E.carrier ⊆ upperHalfPlane := by
    rintro z ⟨w, hw, rfl⟩
    change 0 < (s • w).im
    simpa only [Complex.smul_im, smul_eq_mul] using mul_pos hs (hhalf hw)
  have hEl : ∀ᶠ t : ℝ in 𝓝[>] 0, (t : Plane) * Complex.I ∈ E.carrier := by
    filter_upwards [eventually_nhdsGT_zero_mul_left hr hline] with t ht
    refine ⟨((r * t : ℝ) : Plane) * Complex.I, ht, ?_⟩
    change s • (((r * t : ℝ) : Plane) * Complex.I) = _
    simp [s, Complex.real_smul, ← mul_assoc, hr.ne']
  have hEq : HasMarkedFlux (scaledValue s u) C := by
    have h := hq.dilate s hs
    change HasMarkedFlux _ (r⁻¹ * (C * r)) at h
    rwa [mul_comm C r, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul] at h
  have hEc : Continuous (scaledValue s u) :=
    continuous_const.mul (hc.comp (continuous_const_smul s⁻¹))
  have hshape := second_area_one_rigidity_at_maximizing_quotient E hA (hu.dilate s hs)
    hEc.continuousOn hEy hEh hEl hEq
  have hx' : |s * x| ≤ C / Real.pi := by
    rw [abs_mul, abs_of_pos hs, mul_comm s, ← div_eq_mul_inv, div_le_iff₀ hr]
    change |x| ≤ C * r / Real.pi at hx
    linarith only [hx, show C / Real.pi * r = C * r / Real.pi by ring]
  have hfront := normalizedFlatPatch_of_abs_le_sharpConstant_div_pi hx'
  rw [← hshape, hE, ← e.image_frontier] at hfront
  apply e.injective.mem_set_image.mp
  change s • (x : Plane) ∈ e '' frontier D.carrier
  simpa only [Complex.real_smul, Complex.ofReal_mul] using hfront

/-- At each maximizing inward supporting normal of a global extremizer, the
closed perpendicular segment centered at the given point, of radius `G(D)/π`,
lies on the actual frontier. The quotient uses the continuous weak torsion solution. -/
theorem second_flat_patch_at_maximizing_normal (D : ConvexDomain)
    (hD : torsionTheory.G D = ENNReal.ofReal
      (spectralConstant secondEigenvalue secondEigenfunction * √D.area))
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D.carrier u g) (hc : Continuous u)
    {p n : Plane} (hp : p ∈ frontier D.carrier) (hn : ‖n‖ = 1)
    (hsup : ∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) n (z - p))
    (hline : ∀ᶠ t : ℝ in 𝓝[>] 0, p + t • n ∈ D.carrier)
    (hq : Tendsto (fun t : ℝ => u (p + t • n) / t) (𝓝[>] 0) (𝓝 (torsionTheory.G D).toReal))
    {x : ℝ} (hx : |x| ≤ (torsionTheory.G D).toReal / Real.pi) :
    p + x • (-Complex.I * n) ∈ frontier D.carrier := by
  let e := normalFrame n hn
  let E := D.inNormalFrame p n hn
  let V (z : Plane) := u (e z + p)
  have hG : (torsionTheory.G D).toReal = spectralConstant secondEigenvalue secondEigenfunction * √E.area := by
    have hC : 0 ≤ spectralConstant secondEigenvalue secondEigenfunction := secondMoments.sharpConstant_pos.le
    rw [hD, ENNReal.toReal_ofReal (mul_nonneg hC (Real.sqrt_nonneg _)),
      show E.area = D.area from D.inNormalFrame_area p n hn]
  have hvert (t : ℝ) : e ((t : Plane) * Complex.I) + p = p + t • n := by
    rw [← Complex.real_smul, map_smul, show e Complex.I = n from normalFrame_I n hn, add_comm]
  have hqE : HasMarkedFlux V (spectralConstant secondEigenvalue secondEigenfunction * √E.area) := by
    rw [← hG]
    simpa only [HasMarkedFlux, V, hvert] using hq
  have hlE : ∀ᶠ t : ℝ in 𝓝[>] 0, (t : Plane) * Complex.I ∈ E.carrier := by
    filter_upwards [hline] with t ht
    apply (D.mem_inNormalFrame p n _ hn).mpr
    change e ((t : Plane) * Complex.I) + p ∈ D.carrier
    rwa [hvert]
  have hf := scaled_flat_patch E (hu.inNormalFrame p n hn) (hc.comp (e.continuous.add continuous_const))
    (D.zero_mem_closure_inNormalFrame p n hn (frontier_subset_closure hp))
    (D.inNormalFrame_subset_upper p n hn hsup) hlE hqE (hG ▸ hx)
  let F := e.toHomeomorph.trans (Homeomorph.addRight p)
  have hE : E.carrier = F ⁻¹' D.carrier := Set.ext fun z => D.mem_inNormalFrame p n z hn
  rw [hE, ← F.preimage_frontier] at hf
  change normalFrame n hn (x : Plane) + p ∈ frontier D.carrier at hf
  simpa only [normalFrame_coordinates, Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add,
    add_comm p] using hf

/-- Lemma 5.1 supplies a physical maximizing frame for each extremizer. Its
unit tangent spans the quantitative patch, with positive radius. -/
theorem second_exists_maximizing_normal_flat_patch (D : ConvexDomain)
    (hD : torsionTheory.G D = ENNReal.ofReal
      (spectralConstant secondEigenvalue secondEigenfunction * √D.area)) :
    ∃ (u : Plane → ℝ) (p n : Plane), Continuous u ∧
      IsWeakTorsion D.carrier u (torsionTheory.solution D).weakGradient ∧
      (∀ x ∉ D.carrier, u x = 0) ∧ (torsionTheory.solution D).value =ᵐ[volume.restrict D.carrier] u ∧
      p ∈ frontier D.carrier ∧ ‖n‖ = 1 ∧
      (∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) n (z - p)) ∧
      (∀ᶠ t : ℝ in 𝓝[>] 0, p + t • n ∈ D.carrier) ∧
      Tendsto (fun t : ℝ => u (p + t • n) / t) (𝓝[>] 0) (𝓝 (torsionTheory.G D).toReal) ∧
      ‖-Complex.I * n‖ = 1 ∧ inner (𝕜 := ℝ) n (-Complex.I * n) = 0 ∧
      0 < (torsionTheory.G D).toReal / Real.pi ∧
      (∀ x : ℝ, |x| ≤ (torsionTheory.G D).toReal / Real.pi →
        p + x • (-Complex.I * n) ∈ frontier D.carrier) := by
  obtain ⟨u, p, n, hc, hu, hz, heq, hp, hn, hs, hl, hq⟩ :=
    torsionTheory.exists_maximizing_normal_quotient D
  refine ⟨u, p, n, hc, hu, hz, heq, hp, hn, hs, hl, hq, ?_, ?_,
    div_pos (torsionTheory.G_toReal_pos D) Real.pi_pos, fun _ hx =>
      second_flat_patch_at_maximizing_normal D hD hu hc hp hn hs hl hq hx⟩
  · simp [hn]
  · have h := (normalFrame n hn).inner_map_map Complex.I (1 : Plane)
    have h1 : normalFrame n hn (1 : Plane) = -Complex.I * n := by
      change (-Complex.I * n) * 1 = _
      exact mul_one _
    simpa [h1, Complex.inner] using h

end Torsion.Spectral

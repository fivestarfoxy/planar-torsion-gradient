module

public import Torsion.RestrictedSpectralSemicircleAdmission
public import Torsion.RestrictedSpectralLattice
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Tactic

/-! # Polynomial multiples of the semicircle belong to the closed restricted form -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace Torsion.Spectral

private abbrev coreBox := Icc (-1:ℝ) 1

private def slopeQuot (f : ℝ → ℝ) (x y : ℝ) := (f y-f x)/(y-x)

private theorem barrier_le_one (x : ℝ) : semicircleBarrier x ≤ 1 := by
  have hh := semicircleBarrier_sq x
  have hm : max (1-x^2) 0 ≤ 1 := max_le (by nlinarith [sq_nonneg x]) (by norm_num)
  nlinarith [semicircleBarrier_nonneg x]

private theorem barrier_zero_off_box {x : ℝ} (hx : x ∉ coreBox) : semicircleBarrier x = 0 := by
  apply semicircleBarrier_zero_exterior
  exact le_of_not_gt (fun h => hx (Ioo_subset_Icc_self (abs_lt.mp h)))

private theorem productSlope_inside (P : ℝ → ℝ) {L B x y : ℝ}
    (hB : |P y| ≤ B) (hL : |P y-P x| ≤ L*|y-x|) :
    slopeQuot (fun t => P t*semicircleBarrier t) x y ^ 2 ≤
      2*B^2*(slopeQuot semicircleBarrier x y)^2 + 2*L^2 := by
  by_cases hxy : y=x
  · subst y; simp [slopeQuot]; positivity
  have hd : 0 < |y-x| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hq : |slopeQuot P x y| ≤ L := by
    rw [slopeQuot,abs_div,div_le_iff₀ hd]
    exact hL
  let A := slopeQuot semicircleBarrier x y
  have he : slopeQuot (fun t => P t*semicircleBarrier t) x y =
      P y*A + semicircleBarrier x*slopeQuot P x y := by
    dsimp [slopeQuot,A]; ring
  have h₁ : |P y * A| ≤ B*|A| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hB (abs_nonneg _)
  have h₂ : |semicircleBarrier x * slopeQuot P x y| ≤ L := by
    rw [abs_mul,abs_of_nonneg (semicircleBarrier_nonneg _)]
    exact (mul_le_mul_of_nonneg_right (barrier_le_one x) (abs_nonneg _)).trans (by simpa using hq)
  have hh := (abs_add_le _ _).trans (add_le_add h₁ h₂)
  have h₃ := sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hh) |>.mpr hh
  rw [sq_abs] at h₃
  rw [he]
  change _ ≤ 2*B^2*A^2 + 2*L^2
  nlinarith [sq_nonneg (B*|A|-L), sq_abs A, sq_nonneg A, sq_abs (P y*A + semicircleBarrier x*slopeQuot P x y)]

private theorem productSlope_outside (P : ℝ → ℝ) {B x y : ℝ}
    (hB : |P x| ≤ B) (hy : y ∉ coreBox) :
    slopeQuot (fun t => P t*semicircleBarrier t) x y ^ 2 ≤
      2*B^2*(slopeQuot semicircleBarrier x y)^2 := by
  have he : slopeQuot (fun t => P t*semicircleBarrier t) x y =
      P x*slopeQuot semicircleBarrier x y := by simp [slopeQuot,barrier_zero_off_box hy]; ring
  have hp : (P x)^2 ≤ B^2 := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hB)).mpr hB |>.trans_eq' (sq_abs _)
  rw [he, mul_pow]
  gcongr
  nlinarith [sq_nonneg B]

private theorem polynomialBarrierKernel (P : ℝ → ℝ) (hc : Continuous P)
    (L : ℝ≥0) (hL : LipschitzOnWith L P coreBox) {B : ℝ} (hB : ∀ x ∈ coreBox, |P x| ≤ B) :
    gagliardoEnergy (fun t => P t*semicircleBarrier t) ≠ ⊤ := by
  let f := fun t => P t*semicircleBarrier t
  let S : Set (ℝ × ℝ) := coreBox ×ˢ coreBox
  let J : ℝ × ℝ → ℝ := S.indicator (fun _ => 2*(L:ℝ)^2)
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hJ : Integrable J volume :=
    (integrableOn_const hS.measure_lt_top.ne).integrable_indicator hS.measurableSet
  let K (p : ℝ × ℝ) := (slopeQuot semicircleBarrier p.1 p.2)^2
  have hK : Integrable K volume := by
    simpa only [K,slopeQuot,div_pow] using semicircleBarrier_gagliardoKernel_integrable
  have hf : Continuous f := hc.mul semicircleBarrier_continuous
  have hm : Measurable (fun p : ℝ × ℝ => (f p.2 - f p.1)^2/(p.2-p.1)^2) :=
    (((hf.measurable.comp measurable_snd).sub (hf.measurable.comp measurable_fst)).pow_const 2).div
      ((measurable_snd.sub measurable_fst).pow_const 2)
  have hd : Integrable (fun p : ℝ × ℝ => (f p.2-f p.1)^2/(p.2-p.1)^2) volume := by
    apply ((hK.const_mul (2*B^2)).add hJ).mono' hm.aestronglyMeasurable
    apply ae_of_all
    rintro ⟨x,y⟩
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)),← div_pow]
    change (slopeQuot f x y)^2 ≤ 2*B^2*K (x,y) + J (x,y)
    by_cases hx : x ∈ coreBox <;> by_cases hy : y ∈ coreBox
    · have hJ' : J (x,y) = 2*(L:ℝ)^2 := indicator_of_mem (show (x,y) ∈ S from ⟨hx,hy⟩) _
      rw [hJ']
      exact productSlope_inside P (hB y hy) (by simpa [Real.dist_eq] using hL.dist_le_mul y hy x hx)
    · have hJ' : J (x,y) = 0 := indicator_of_notMem (show (x,y) ∉ S from fun h => hy h.2) _
      rw [hJ',add_zero]
      exact productSlope_outside P (hB x hx) hy
    · have hJ' : J (x,y) = 0 := indicator_of_notMem (show (x,y) ∉ S from fun h => hx h.1) _
      have hswap (g : ℝ → ℝ) : slopeQuot g x y = slopeQuot g y x := by
        dsimp [slopeQuot]; rw [← neg_sub (g x) (g y), ← neg_sub x y,neg_div_neg_eq]
      rw [hJ',add_zero]
      change (slopeQuot f x y)^2 ≤ 2*B^2*(slopeQuot semicircleBarrier x y)^2
      rw [hswap f, hswap semicircleBarrier]
      exact productSlope_outside P (hB y hy) hx
    · have hJ' : J (x,y) = 0 := indicator_of_notMem (show (x,y) ∉ S from fun h => hx h.1) _
      simp [f,K,slopeQuot,barrier_zero_off_box hx,barrier_zero_off_box hy,hJ']
  rw [gagliardoEnergy_eq_double hf.measurable,← lintegral_prod _ (measurable_gagliardoKernel hf.measurable).aemeasurable]
  exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (ae_of_all _ fun p => div_nonneg (sq_nonneg _) (sq_nonneg _))).2 hd

/-- Multiplication by any polynomial preserves admission of the semicircle
weight to the original zero-exterior, Fourier-defined restricted form. -/
theorem polynomial_semicircle_memRestrictedFormDomain (p : Polynomial ℝ) :
    MemRestrictedFormDomain (fun x => p.eval x * semicircleBarrier x) := by
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image
    (K := coreBox) (f := fun x => |p.eval x|) (p.continuous.abs.continuousOn)
  have hb (x : ℝ) (hx : x ∈ coreBox) : |p.eval x| ≤ B := hB (mem_image_of_mem _ hx)
  let P := fun x => p.eval x + B
  have hp : ContDiff ℝ ∞ (fun x : ℝ => p.eval x) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using p.contDiff_aeval (𝕜 := ℝ) (∞ : WithTop ℕ∞)
  have hc : ContDiff ℝ ∞ P := hp.add contDiff_const
  have hc1 : ContDiff ℝ 1 P := hc.of_le (by simp)
  obtain ⟨L,hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
    (ContDiffOn.locallyLipschitzOn (convex_Icc _ _) (hc1.contDiffOn (s := coreBox)))
  have hP (x : ℝ) (hx : x ∈ coreBox) : |P x| ≤ B+|B| :=
    (abs_add_le _ _).trans (add_le_add (hb x hx) (le_refl _))
  have hG := polynomialBarrierKernel P hc.continuous L hL hP
  have hpos (x : ℝ) : 0 ≤ P x * semicircleBarrier x := by
    by_cases hx : x ∈ coreBox
    · exact mul_nonneg (by dsimp [P]; linarith [neg_abs_le (p.eval x),hb x hx]) (semicircleBarrier_nonneg _)
    · simp [barrier_zero_off_box hx]
  have hA := (memRestrictedFormDomain_of_nonnegative_gagliardo
    (hc.continuous.mul semicircleBarrier_continuous) (hc.contDiffOn.mul semicircleBarrier_contDiffOn)
    (fun x hx => by change P x * semicircleBarrier x = 0; rw [semicircleBarrier_zero_exterior x (le_of_not_gt (fun h => hx (abs_lt.mp h))),mul_zero])
    hpos hG).1
  convert hA.sub (semicircleBarrier_memRestrictedFormDomain.const_mul B) using 1
  funext x
  dsimp [P]
  ring

end Torsion.Spectral

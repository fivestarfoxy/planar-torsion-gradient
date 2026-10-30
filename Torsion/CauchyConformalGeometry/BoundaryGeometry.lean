module

public import Torsion.CauchyConformalGeometry.ImageSeparation
public import Torsion.CauchyConformalGeometry.BoundaryDerivative
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Simplicity of the actual Cauchy free arc

The strict real-part separation persists to the actual boundary extension,
including both support endpoints. The monotone height then distinguishes
all points of the free arc.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

theorem profile_nonneg_Icc_of_pos_odd_zero {φ : ℝ → ℝ}
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ φ s := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h | h
  · have ho := hodd 0
    simp only [neg_zero] at ho
    rw [← h]
    linarith
  · rcases lt_or_eq_of_le hs.2 with h' | h'
    · exact (hpos s ⟨h, h'⟩).le
    · rw [h', hzero 1 (by norm_num)]

private theorem log_ratio_mono {A B u v : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hu : 0 < u) (huv : u ≤ v) :
    Real.log (A + u) - Real.log (B + u) ≤ Real.log (A + v) - Real.log (B + v) := by
  have hAu : 0 < A + u := add_pos_of_nonneg_of_pos hA hu
  have hBu : 0 < B + u := add_pos_of_nonneg_of_pos (hA.trans hAB) hu
  have hAv : 0 < A + v := hAu.trans_le (add_le_add_left huv A)
  have hBv : 0 < B + v := hBu.trans_le (add_le_add_left huv B)
  rw [← Real.log_div hAu.ne' hBu.ne', ← Real.log_div hAv.ne' hBv.ne']
  apply Real.log_le_log (div_pos hAu hBu)
  apply (div_le_div_iff₀ hBu hBv).2
  nlinarith [mul_nonneg (sub_nonneg.2 hAB) (sub_nonneg.2 huv)]

/-- At positive horizontal coordinate the real Cauchy value increases as
the height increases. Thus approaching the real boundary preserves a
strictly negative upper bound from any fixed interior height. -/
theorem cauchy_re_mono_vertical {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {x y Y : ℝ} (hx : 0 < x) (hy : 0 < y) (hyY : y ≤ Y) :
    (cauchy φ ((x : ℂ) + (y : ℂ) * Complex.I)).re ≤
      (cauchy φ ((x : ℂ) + (Y : ℂ) * Complex.I)).re := by
  have hY : 0 < Y := hy.trans_le hyY
  have heq (t : ℝ) (ht : 0 < t) :
      (cauchy φ ((x : ℂ) + (t : ℂ) * Complex.I)).re = (Real.pi⁻¹ / 2) *
        ∫ s in (0 : ℝ)..1, φ s *
          (Real.log ((x - s) ^ 2 + t ^ 2) - Real.log ((x + s) ^ 2 + t ^ 2)) := by
    have hz : (x : ℂ) + (t : ℂ) * Complex.I ∈ upperHalfPlane := by
      simpa [upperHalfPlane] using ht
    rw [cauchy_re_eq_log_integral hφ hodd hzero hz]
    simpa using congrArg (fun q : ℝ => (Real.pi⁻¹ / 2) * q)
      (odd_log_integral_pair hφ hodd ht)
  rw [heq y hy, heq Y hY]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ Real.pi⁻¹ / 2)
  have hcont (t : ℝ) (ht : 0 < t) : Continuous (fun s : ℝ => φ s *
      (Real.log ((x - s) ^ 2 + t ^ 2) - Real.log ((x + s) ^ 2 + t ^ 2))) := by
    apply hφ.mul
    apply Continuous.sub
    · exact (by fun_prop : Continuous (fun s : ℝ => (x - s) ^ 2 + t ^ 2)).log
        (fun s => ne_of_gt (by positivity))
    · exact (by fun_prop : Continuous (fun s : ℝ => (x + s) ^ 2 + t ^ 2)).log
        (fun s => ne_of_gt (by positivity))
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    ((hcont y hy).intervalIntegrable 0 1) ((hcont Y hY).intervalIntegrable 0 1)
  intro s hs
  apply mul_le_mul_of_nonneg_left _ (profile_nonneg_Icc_of_pos_odd_zero hodd hzero hpos s hs)
  apply log_ratio_mono (sq_nonneg (x - s))
  · nlinarith [mul_nonneg hx.le hs.1]
  · exact sq_pos_of_pos hy
  · exact pow_le_pow_left₀ hy.le hyY 2

/-- Strict real-part separation holds on the genuine boundary extension,
including the endpoints. No endpoint principal-value formula is assumed. -/
theorem cauchy_boundary_re_neg_of_pos {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) {x : ℝ} (hx : 0 < x) :
    (cauchyExtension φ (x : ℂ)).re < 0 := by
  have hc := hφ.continuous hα0
  have hext := cauchy_extensions_diffContOnCl_of_holder hφ hα0 hα1 hodd hzero
  let z : ℕ → ℂ := fun n => (x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I
  have hz (n : ℕ) : z n ∈ upperHalfPlane := by
    simp only [z, upperHalfPlane, mem_setOf_eq, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
    positivity
  have hlim : Tendsto z atTop (𝓝 (x : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [z] using tendsto_const_nhds.add (h.mul_const Complex.I)
  have hvalue : Tendsto (fun n => (cauchy φ (z n)).re) atTop
      (𝓝 ((cauchyExtension φ (x : ℂ)).re)) := by
    have h := (hext.1.continuousOn _ (ofReal_mem_closure_upperHalfPlane x)).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlim
        (Eventually.of_forall fun n => subset_closure (hz n)))
    apply (Complex.continuous_re.tendsto _ |>.comp h).congr'
    exact Eventually.of_forall fun n => congrArg Complex.re (cauchyExtension_eq hc.continuousOn (hz n))
  have hbound : ∀ n : ℕ, (cauchy φ (z n)).re ≤ (cauchy φ ((x : ℂ) + Complex.I)).re := by
    intro n
    have hn : 0 < (1 / ((n : ℝ) + 1) : ℝ) := by positivity
    have hn1 : (1 / ((n : ℝ) + 1) : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
      linarith [Nat.cast_nonneg (α := ℝ) n]
    simpa [z] using cauchy_re_mono_vertical hc hodd hzero hpos hx hn hn1
  have hle : (cauchyExtension φ (x : ℂ)).re ≤ (cauchy φ ((x : ℂ) + Complex.I)).re :=
    le_of_tendsto hvalue (Eventually.of_forall hbound)
  exact hle.trans_lt (cauchy_re_neg_of_re_pos hc hodd hzero hpos
    (by simp [upperHalfPlane]) (by simpa using hx))

/-- The positive half of the actual height is strictly decreasing, including
its endpoints. -/
theorem height_strictAntiOn_Icc {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    StrictAntiOn (height φ) (Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1) (height_continuous hφ.continuousOn).continuousOn
  intro x hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
  rw [deriv_height_eq hφ hodd hzero x]
  exact neg_neg_of_pos (hpos x hx')

/-- The actual values on a concrete vertical sequence converge to the
genuine closed-half-plane boundary extension. -/
theorem cauchy_boundary_vertical_tendsto_seq {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) (x : ℝ) :
    Tendsto (fun n : ℕ => cauchy φ
      ((x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)) atTop
      (𝓝 (cauchyExtension φ (x : ℂ))) := by
  have hc := hφ.continuous hα0
  have hext := cauchy_extensions_diffContOnCl_of_holder hφ hα0 hα1 hodd hzero
  have hz (n : ℕ) : (x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I
      ∈ upperHalfPlane := by
    simp only [upperHalfPlane, mem_setOf_eq, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
    positivity
  have hp : Tendsto (fun n : ℕ =>
      (x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop (𝓝 (x : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add (h.mul_const Complex.I)
  have hv := (hext.1.continuousOn _ (ofReal_mem_closure_upperHalfPlane x)).tendsto.comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hp
      (Eventually.of_forall fun n => subset_closure (hz n)))
  apply hv.congr'
  exact Eventually.of_forall fun n => cauchyExtension_eq hc.continuousOn (hz n)

/-- The actual real boundary coordinate is odd. Its parity follows by
taking limits of the proved interior integral symmetry. -/
theorem cauchy_boundary_re_odd {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) :
    Function.Odd (fun x : ℝ => (cauchyExtension φ (x : ℂ)).re) := by
  intro x
  have hc := hφ.continuous hα0
  have hminus := Complex.continuous_re.tendsto _ |>.comp
    (cauchy_boundary_vertical_tendsto_seq hφ hα0 hα1 hodd hzero (-x))
  have hplus := (Complex.continuous_re.tendsto _ |>.comp
    (cauchy_boundary_vertical_tendsto_seq hφ hα0 hα1 hodd hzero x)).neg
  have heq (n : ℕ) :
      (cauchy φ ((-x : ℝ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)).re =
        -(cauchy φ ((x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)).re := by
    have hz : (x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I ∈ upperHalfPlane := by
      have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simpa only [upperHalfPlane, mem_setOf_eq, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
        mul_one, zero_mul, add_zero, zero_add] using hp
    have hreflect : -star ((x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) =
        ((-x : ℝ) : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    simpa only [hreflect] using cauchy_re_neg_conj hc hodd hzero hz
  exact tendsto_nhds_unique hminus (hplus.congr' (Eventually.of_forall fun n => (heq n).symm))

theorem cauchy_boundary_re_pos_of_neg {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) {x : ℝ} (hx : x < 0) :
    0 < (cauchyExtension φ (x : ℂ)).re := by
  have h := cauchy_boundary_re_neg_of_pos hφ hα0 hα1 hodd hzero hpos (neg_pos.2 hx)
  have ho := cauchy_boundary_re_odd hφ hα0 hα1 hodd hzero x
  dsimp only at ho
  rw [ho] at h
  linarith

/-- The free boundary arc is genuinely simple, including its two distinct
endpoints. Equality of heights first determines the absolute parameter;
the strict real-coordinate signs separate the reflected halves. -/
theorem cauchy_boundary_injOn_interval {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    InjOn (fun x : ℝ => cauchyExtension φ (x : ℂ)) (Icc (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  have hheight : height φ x = height φ y := by
    simpa only [cauchyExtension_ofReal, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add] using congrArg Complex.im hxy
  have habs : |x| = |y| := (height_strictAntiOn_Icc (hφ.continuous hα0) hodd hzero hpos).injOn
    ⟨abs_nonneg x, abs_le.2 hx⟩ ⟨abs_nonneg y, abs_le.2 hy⟩ (by
      simpa only [height, abs_abs] using hheight)
  rcases eq_or_eq_neg_of_sq_eq_sq x y ((sq_eq_sq_iff_abs_eq_abs x y).2 habs) with heq | heq
  · exact heq
  · have hre := congrArg Complex.re hxy
    rcases lt_trichotomy x 0 with hxn | hxn | hxp
    · have hyn : 0 < y := by linarith
      have h1 := cauchy_boundary_re_pos_of_neg hφ hα0 hα1 hodd hzero hpos hxn
      have h2 := cauchy_boundary_re_neg_of_pos hφ hα0 hα1 hodd hzero hpos hyn
      linarith
    · linarith
    · have hyn : y < 0 := by linarith
      have h1 := cauchy_boundary_re_neg_of_pos hφ hα0 hα1 hodd hzero hpos hxp
      have h2 := cauchy_boundary_re_pos_of_neg hφ hα0 hα1 hodd hzero hpos hyn
      linarith

/-- The open free arc lies strictly above the real axis and therefore does
not meet any point of the joining real segment. -/
theorem cauchy_freeArc_disjoint_realAxis {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    Disjoint ((fun x : ℝ => cauchyExtension φ (x : ℂ)) '' Ioo (-1 : ℝ) 1)
      (range (fun t : ℝ => (t : ℂ))) := by
  apply disjoint_left.2
  rintro w ⟨x, hx, rfl⟩ ⟨t, ht⟩
  have hp := height_pos hφ hpos (abs_lt.2 hx)
  have heq := congrArg Complex.im ht
  simp only [cauchyExtension_ofReal, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, zero_add] at heq
  exact hp.ne' heq.symm

/-- The closed free arc is a closed topological embedding of the compact
parameter interval, in addition to the pointwise injectivity proved above. -/
theorem cauchy_boundary_isClosedEmbedding {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    Topology.IsClosedEmbedding (fun x : Icc (-1 : ℝ) 1 =>
      cauchyExtension φ ((x : ℝ) : ℂ)) := by
  have hc : Continuous (fun x : Icc (-1 : ℝ) 1 => cauchyExtension φ ((x : ℝ) : ℂ)) :=
    (cauchy_boundary_contDiff_one hφ hα0 hα1 hodd hzero).continuous.comp continuous_subtype_val
  apply hc.isClosedEmbedding
  intro x y heq
  exact Subtype.ext (cauchy_boundary_injOn_interval hφ hα0 hα1 hodd hzero hpos x.property y.property heq)

/-- The two free-arc endpoints are distinct real points on opposite sides
of zero. This identifies the nondegenerate joining segment. -/
theorem cauchy_boundary_endpoints {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    (cauchyExtension φ (-1 : ℂ)).im = 0 ∧ (cauchyExtension φ (1 : ℂ)).im = 0 ∧
      0 < (cauchyExtension φ (-1 : ℂ)).re ∧ (cauchyExtension φ (1 : ℂ)).re < 0 := by
  have him (x : ℝ) : (cauchyExtension φ (x : ℂ)).im = height φ x := by
    simp only [cauchyExtension_ofReal, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (him (-1)).trans (height_zero_of_one_le_abs φ (by norm_num))
  · simpa using (him 1).trans (height_zero_of_one_le_abs φ (by norm_num))
  · simpa using cauchy_boundary_re_pos_of_neg hφ hα0 hα1 hodd hzero hpos
      (show (-1 : ℝ) < 0 by norm_num)
  · simpa using cauchy_boundary_re_neg_of_pos hφ hα0 hα1 hodd hzero hpos
      (show (0 : ℝ) < 1 by norm_num)

end Torsion.Spectral

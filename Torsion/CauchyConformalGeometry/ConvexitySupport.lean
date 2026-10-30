module

public import Torsion.CauchyConformalGeometry.ConvexitySlope
public import Torsion.CauchyConformalGeometry.ConvexityNormals

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Supporting tangent lines for the actual Cauchy boundary

On the positive half of the free arc, the monotone ratio `v/φ` makes the
signed tangent-chord function decrease up to its tangency parameter and
increase afterwards. Reflection and the exact flat-segment description
then give supporting lines for the entire actual frontier.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The support functional evaluated on the actual boundary has the
Wronskian derivative needed for its minimum at the tangency parameter. -/
theorem cauchySupport_boundary_hasDerivAt {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (t : ℝ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => cauchySupport a b φ t (cauchyExtension φ (r : ℂ)))
      (φ t * boundaryVelocity a b φ s - boundaryVelocity a b φ t * φ s) s := by
  have h := ((cauchySupportFunctional a b φ t).hasFDerivAt.comp_hasDerivAt s
    (cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero s)).sub_const
      (cauchySupportFunctional a b φ t (cauchyExtension φ (t : ℂ)))
  rw [cauchy_boundary_tangent_eq hφ hα0 hzero hlinear hs] at h
  simpa [Function.comp_def, cauchySupport, cauchySupportFunctional,
    Complex.reCLM_apply, Complex.imCLM_apply, sub_eq_add_neg, mul_add, add_mul,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- Every tangent on the positive half of the actual free arc supports
that whole half-arc, including both endpoints. -/
theorem cauchySupport_nonneg_positive_half {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)
    {t s : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ cauchySupport a b φ t (cauchyExtension φ (s : ℂ)) := by
  let G : ℝ → ℝ := fun r => cauchySupport a b φ t (cauchyExtension φ (r : ℂ))
  have hcont : Continuous G := by
    exact ((cauchySupportFunctional a b φ t).continuous.comp
      (cauchy_boundary_contDiff_one hφ hα0 hα1 hodd hzero).continuous).sub continuous_const
  have hdiff : Differentiable ℝ G := by
    intro r
    exact (((cauchySupportFunctional a b φ t).hasFDerivAt.comp_hasDerivAt r
      (cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero r)).sub_const
        (cauchySupportFunctional a b φ t (cauchyExtension φ (t : ℂ)))).differentiableAt
  have hratio := boundaryVelocity_div_profile_strictMonoOn
    ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd
  have hleft : AntitoneOn G (Icc (0 : ℝ) t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) t) hcont.continuousOn hdiff.differentiableOn
    intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) t := by simpa only [interior_Icc] using hr
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr'.1, hr'.2.trans ht.2⟩
    change deriv (fun r : ℝ => cauchySupport a b φ t (cauchyExtension φ (r : ℂ))) r ≤ 0
    rw [(cauchySupport_boundary_hasDerivAt hφ hα0 hα1 hodd hzero hlinear t
      (show r ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hr01.1], hr01.2.le⟩)).deriv]
    have hm := hratio.monotoneOn hr01 ht hr'.2.le
    have hm' := (div_le_div_iff₀ (hpos r hr01) (hpos t ht)).1 hm
    nlinarith
  have hright : MonotoneOn G (Icc t (1 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t (1 : ℝ)) hcont.continuousOn hdiff.differentiableOn
    intro r hr
    have hr' : r ∈ Ioo t (1 : ℝ) := by simpa only [interior_Icc] using hr
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨ht.1.trans hr'.1, hr'.2⟩
    change 0 ≤ deriv (fun r : ℝ => cauchySupport a b φ t (cauchyExtension φ (r : ℂ))) r
    rw [(cauchySupport_boundary_hasDerivAt hφ hα0 hα1 hodd hzero hlinear t
      (show r ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hr01.1], hr01.2.le⟩)).deriv]
    have hm := hratio.monotoneOn ht hr01 hr'.1.le
    have hm' := (div_le_div_iff₀ (hpos t ht) (hpos r hr01)).1 hm
    nlinarith
  by_cases hst : s ≤ t
  · have hm := hleft (show s ∈ Icc (0 : ℝ) t from ⟨hs.1, hst⟩)
      (show t ∈ Icc (0 : ℝ) t from ⟨ht.1.le, le_rfl⟩) hst
    simpa only [G, cauchySupport_self] using hm
  · have hts : t ≤ s := (lt_of_not_ge hst).le
    have hm := hright (show t ∈ Icc t (1 : ℝ) from ⟨le_rfl, ht.2.le⟩)
      (show s ∈ Icc t (1 : ℝ) from ⟨hts, hs.2⟩) hts
    simpa only [G, cauchySupport_self] using hm


/-- A tangent on the positive half supports both halves of the complete
free arc. The reflected half lies farther into the supporting half-plane. -/
theorem cauchySupport_nonneg_freeArc_of_pos {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)
    {t s : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Icc (-1 : ℝ) 1) :
    0 ≤ cauchySupport a b φ t (cauchyExtension φ (s : ℂ)) := by
  by_cases hs0 : 0 ≤ s
  · exact cauchySupport_nonneg_positive_half ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd ht
      ⟨hs0, hs.2⟩
  · have hsneg : s < 0 := lt_of_not_ge hs0
    have hminus : -s ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hs.1]⟩
    have hq := cauchySupport_nonneg_positive_half ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd ht hminus
    have hX := cauchy_boundary_re_pos_of_neg hφ hα0 hα1 hodd hzero hpos hsneg
    have ho := cauchy_boundary_re_odd hφ hα0 hα1 hodd hzero s
    dsimp only at ho
    have hY := height_even φ s
    have him (r : ℝ) : (cauchyExtension φ (r : ℂ)).im = height φ r := by
      simp [cauchyExtension_ofReal]
    rw [cauchySupport_eq, him] at hq ⊢
    rw [ho, hY] at hq
    nlinarith [mul_nonneg (hpos t ht).le hX.le]

/-- A positive-half free tangent also supports every point of the exact
flat segment, whose minimum for this normal is its left endpoint. -/
theorem cauchySupport_nonneg_flatSegment_of_pos {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)
    {t r : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hr : (cauchyExtension φ (1 : ℂ)).re ≤ r) :
    0 ≤ cauchySupport a b φ t (r : ℂ) := by
  have hq := cauchySupport_nonneg_positive_half ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd ht
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from by norm_num)
  have him : (cauchyExtension φ (1 : ℂ)).im = 0 :=
    (cauchy_boundary_endpoints hφ hα0 hα1 hodd hzero hpos).2.1
  rw [cauchySupport_eq] at hq ⊢
  simp only [Complex.ofReal_one, him] at hq
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [mul_nonneg (hpos t ht).le (sub_nonneg.2 hr)]

/-- Every positive-half free tangent supports the entire actual frontier,
using the proved exact free-arc and flat-segment decomposition. -/
theorem cauchySupport_nonneg_frontier_of_pos {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {w : ℂ} (hw : w ∈ frontier (cauchyImage φ)) :
    0 ≤ cauchySupport a b φ t w := by
  rw [frontier_cauchyImage_freeArc_union_segment hφ hα0 hα1 hodd hzero hpos] at hw
  rcases hw with ⟨s, hs, rfl⟩ | ⟨r, hr, rfl⟩
  · exact cauchySupport_nonneg_freeArc_of_pos ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd ht hs
  · exact cauchySupport_nonneg_flatSegment_of_pos ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd ht hr.1

/-- Every tangent of the actual closed free arc is a supporting line of
the entire actual frontier, including the central point and both joins. -/
theorem cauchySupport_nonneg_frontier {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {w : ℂ} (hw : w ∈ frontier (cauchyImage φ)) :
    0 ≤ cauchySupport a b φ t w := by
  rcases lt_trichotomy t 0 with htneg | ht0 | htpos
  · rcases eq_or_lt_of_le ht.1 with htend | htint
    · have he := (cauchySupport_endpoints_nonneg ha hφ hα0 hα1 hodd hzero hpos hlinear hw).1
      simpa only [← htend] using he
    · have hreflect := cauchy_frontier_neg_conj_mem hφ hα0 hα1 hodd hzero hpos hw
      have hq := cauchySupport_nonneg_frontier_of_pos ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd
        (t := -t) (show -t ∈ Ioo (0 : ℝ) 1 from ⟨by linarith, by linarith⟩) hreflect
      rwa [cauchySupport_neg_conj hφ hα0 hα1 hodd hzero] at hq
  · subst t
    exact cauchySupport_zero_nonneg ha hφ hα0 hα1 hodd hzero hpos hlinear hw
  · rcases lt_or_eq_of_le ht.2 with htint | htend
    · exact cauchySupport_nonneg_frontier_of_pos ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd
        ⟨htpos, htint⟩ hw
    · have he := (cauchySupport_endpoints_nonneg ha hφ hα0 hα1 hodd hzero hpos hlinear hw).2
      simpa only [htend] using he

end Torsion.Spectral

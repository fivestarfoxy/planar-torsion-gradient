module

public import Torsion.CauchyConformalGeometry.CompactifiedBoundary

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual flat segment of the Cauchy image

Strict monotonicity and the actual zero limit at infinity show that the two
exterior rays trace precisely the two halves of the joining real segment.
Thus the actual frontier is exactly the closed free arc together with this
nondegenerate straight segment.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- Every real point between the right free-arc endpoint and zero is
attained exactly on the right exterior branch. -/
theorem cauchy_boundary_exterior_right_surjOn {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) :
    SurjOn (fun x : ℝ => cauchyExtension φ (x : ℂ)) (Ici 1)
      (Complex.ofReal '' Ico (cauchyExtension φ (1 : ℂ)).re 0) := by
  rintro w ⟨s, hs, rfl⟩
  have hlim : Tendsto (fun x : ℝ => (cauchyExtension φ (x : ℂ)).re) atTop (𝓝 0) := by
    have hn : Tendsto (fun x : ℝ => ‖(x : ℂ)‖) atTop atTop := by
      simpa only [Complex.norm_real] using tendsto_norm_atTop_atTop
    have h := (Complex.continuous_re.tendsto 0).comp
      (cauchy_tendsto_zero (hφ.continuous hα0).continuousOn hn)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact congrArg Complex.re (cauchyExtension_ofReal_exterior hφ hα0 hα1 hodd hzero
      (by rw [abs_of_pos (by linarith : 0 < x)]; exact hx)).symm
  obtain ⟨t, ht1, hst⟩ := ((eventually_gt_atTop (1 : ℝ)).and
    (hlim.eventually (eventually_gt_nhds hs.2))).exists
  have hc : ContinuousOn (fun x : ℝ => (cauchyExtension φ (x : ℂ)).re) (Ici 1) :=
    (Complex.continuous_re.comp
      (cauchy_boundary_contDiff_one hφ hα0 hα1 hodd hzero).continuous).continuousOn
  obtain ⟨x, hx, hxs⟩ := hc.surjOn_Icc (show (1 : ℝ) ∈ Ici 1 from by norm_num)
    (show t ∈ Ici 1 from ht1.le) ⟨hs.1, hst.le⟩
  refine ⟨x, hx, ?_⟩
  change 1 ≤ x at hx
  apply Complex.ext
  · simpa using hxs
  · have hxabs : 1 ≤ |x| := by rw [abs_of_nonneg (by linarith : 0 ≤ x)]; exact hx
    simp [cauchyExtension_ofReal, height_zero_of_one_le_abs φ hxabs]

/-- Exact frontier decomposition into the actual closed free arc and the
straight real segment joining its two endpoints. -/
theorem frontier_cauchyImage_freeArc_union_segment {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    frontier (cauchyImage φ) =
      (fun x : ℝ => cauchyExtension φ (x : ℂ)) '' Icc (-1 : ℝ) 1 ∪
      Complex.ofReal '' Icc (cauchyExtension φ (1 : ℂ)).re
        (cauchyExtension φ (-1 : ℂ)).re := by
  classical
  have hep := cauchy_boundary_endpoints hφ hα0 hα1 hodd hzero hpos
  have hneg := hep.2.2.2
  have hposend := hep.2.2.1
  have hoddre := cauchy_boundary_re_odd hφ hα0 hα1 hodd hzero
  rw [frontier_cauchyImage_eq (hφ.continuous hα0) hodd hzero hpos]
  apply Subset.antisymm
  · rintro w (⟨x, rfl⟩ | hw)
    · by_cases hx : x ∈ Icc (-1 : ℝ) 1
      · exact Or.inl ⟨x, hx, rfl⟩
      · right
        have hxabs : 1 ≤ |x| := by
          by_contra! habs
          exact hx ⟨(abs_lt.1 habs).1.le, (abs_lt.1 habs).2.le⟩
        refine ⟨(cauchyExtension φ (x : ℂ)).re, ?_, ?_⟩
        · rcases lt_or_ge x (-1) with hxleft | hxleft
          · refine ⟨hneg.le.trans (cauchy_boundary_re_pos_of_neg hφ hα0 hα1 hodd hzero hpos
                (by linarith : x < 0)).le, ?_⟩
            have hb := (cauchy_boundary_re_strictMonoOn_Iic hφ hα0 hα1 hodd hzero hpos).monotoneOn
              (a := x) (b := (-1 : ℝ)) (show x ∈ Iic (-1) from hxleft.le)
              (show (-1 : ℝ) ∈ Iic (-1) from by norm_num) hxleft.le
            simpa only [Complex.ofReal_neg, Complex.ofReal_one] using hb
          · have hxright : 1 < x := lt_of_not_ge (fun hxle => hx ⟨hxleft, hxle⟩)
            refine ⟨?_, (cauchy_boundary_re_neg_of_pos hφ hα0 hα1 hodd hzero hpos
                (by linarith : 0 < x)).le.trans hposend.le⟩
            have hb := (cauchy_boundary_re_strictMonoOn_Ici hφ hα0 hα1 hodd hzero hpos).monotoneOn
              (a := (1 : ℝ)) (b := x) (show (1 : ℝ) ∈ Ici 1 from by norm_num)
              (show x ∈ Ici 1 from hxright.le) hxright.le
            simpa only [Complex.ofReal_one] using hb
        · apply Complex.ext
          · simp
          · simp [cauchyExtension_ofReal, height_zero_of_one_le_abs φ hxabs]
    · right
      refine ⟨0, ⟨hneg.le, hposend.le⟩, ?_⟩
      simpa only [Complex.ofReal_zero] using (mem_singleton_iff.1 hw).symm
  · rintro w (⟨x, _, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact Or.inl ⟨x, rfl⟩
    · rcases lt_trichotomy s 0 with hsneg | hs0 | hspos
      · have hm := cauchy_boundary_exterior_right_surjOn hφ hα0 hα1 hodd hzero
          (show (s : ℂ) ∈ Complex.ofReal '' Ico (cauchyExtension φ (1 : ℂ)).re 0 from
            ⟨s, ⟨hs.1, hsneg⟩, rfl⟩)
        obtain ⟨x, _, hx⟩ := hm
        exact Or.inl ⟨x, hx⟩
      · exact Or.inr (by simp [hs0])
      · have hleft : (cauchyExtension φ (1 : ℂ)).re ≤ -s := by
          have ho := hoddre 1
          norm_num at ho
          linarith [hs.2]
        obtain ⟨x, _, hx⟩ := cauchy_boundary_exterior_right_surjOn hφ hα0 hα1 hodd hzero
          (show ((-s : ℝ) : ℂ) ∈ Complex.ofReal '' Ico (cauchyExtension φ (1 : ℂ)).re 0 from
            ⟨-s, ⟨hleft, neg_neg_of_pos hspos⟩, rfl⟩)
        refine Or.inl ⟨-x, ?_⟩
        change cauchyExtension φ ((-x : ℝ) : ℂ) = (s : ℂ)
        dsimp only at hx
        rw [cauchy_boundary_neg_conj hφ hα0 hα1 hodd hzero x, hx]
        simp

end Torsion.Spectral

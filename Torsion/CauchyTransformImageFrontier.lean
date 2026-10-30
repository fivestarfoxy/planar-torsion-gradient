import Torsion.CauchyTransformImageBound
import Torsion.CauchyConformalGeometry.Inverse

/-!
# The actual frontier of the Cauchy image

Compactness of bounded preimages, the proved boundary extension, and decay
at infinity locate every frontier point on the real boundary curve or at
the image of infinity. No Jordan boundary theorem is assumed.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace Torsion.Spectral

private theorem cauchy_small_on_exterior {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R < ‖z‖ → ‖cauchy φ z‖ < ε := by
  have hc : ContinuousOn (fun s : ℝ => (height φ s : ℂ)) (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp (height_continuous hφ)).continuousOn
  let C : ℝ := ‖(Real.pi : ℂ)⁻¹‖ * ∫ s in Icc (-1 : ℝ) 1, ‖(height φ s : ℂ)‖
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨2 + C / ε, by positivity, ?_⟩
  intro z hz
  have hnorm : 1 < ‖z‖ := by linarith [div_nonneg hC hε.le]
  have hbound : ‖cauchy φ z‖ ≤ C / (‖z‖ - 1) := by
    unfold cauchy
    rw [norm_mul, norm_neg]
    simpa only [C, mul_div_assoc] using
      mul_le_mul_of_nonneg_left (norm_cauchy_integral_le hc hnorm) (norm_nonneg ((Real.pi : ℂ)⁻¹))
  apply hbound.trans_lt
  apply (div_lt_iff₀ (sub_pos.2 hnorm)).2
  have hCe : C / ε * ε = C := div_mul_cancel₀ C hε.ne'
  nlinarith

/-- Every frontier point of the actual image is on the genuine real
boundary curve, or is the zero limit at infinity. -/
theorem frontier_cauchyImage_subset {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    frontier (cauchyImage φ) ⊆
      range (fun x : ℝ => cauchyExtension φ (x : ℂ)) ∪ {0} := by
  intro p hp
  by_cases hp0 : p = 0
  · exact Or.inr hp0
  have hpε : 0 < ‖p‖ / 2 := half_pos (norm_pos_iff.2 hp0)
  obtain ⟨R, hR, hdecay⟩ := cauchy_small_on_exterior hφ.continuousOn hpε
  obtain ⟨CY, hY⟩ := height_exists_holder (α := 1) hφ hodd hzero le_rfl
  have hE := (cauchyExtension_diffContOnCl hY (by norm_num)).continuousOn
  let K : Set ℂ := closure upperHalfPlane ∩ closedBall 0 R
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).inter_left isClosed_closure
  have himageclosed : IsClosed (cauchyExtension φ '' K) :=
    (hK.image_of_continuousOn (hE.mono inter_subset_left)).isClosed
  have hlocal : ball p (‖p‖ / 2) ∩ cauchyImage φ ⊆ cauchyExtension φ '' K := by
    rintro _ ⟨hwball, z, hz, rfl⟩
    have hnorm : ‖z‖ ≤ R := by
      by_contra! h
      have hzsmall := hdecay z h
      have hdist : ‖cauchy φ z - p‖ < ‖p‖ / 2 := by
        simpa only [mem_ball, dist_eq_norm] using hwball
      have htri : ‖p‖ ≤ ‖cauchy φ z - p‖ + ‖cauchy φ z‖ := by
        have ht := norm_sub_le (cauchy φ z) (cauchy φ z - p)
        simpa only [sub_sub_cancel, add_comm] using ht
      linarith
    refine ⟨z, ⟨subset_closure hz, ?_⟩, cauchyExtension_eq hφ.continuousOn hz⟩
    simpa only [mem_closedBall, dist_zero_right] using hnorm
  have hpcl : p ∈ closure (ball p (‖p‖ / 2) ∩ cauchyImage φ) :=
    isOpen_ball.inter_closure ⟨mem_ball_self hpε, frontier_subset_closure hp⟩
  have hpmem : p ∈ cauchyExtension φ '' K := closure_minimal hlocal himageclosed hpcl
  obtain ⟨z, hzK, hzp⟩ := hpmem
  have hznonneg : 0 ≤ z.im :=
    (closure_minimal (s := upperHalfPlane) (t := {w : ℂ | 0 ≤ w.im})
      (fun w hw => (show 0 < w.im from hw).le)
      (isClosed_le continuous_const Complex.continuous_im)) hzK.1
  have hz0 : z.im = 0 := by
    by_contra hz0
    have hzh : z ∈ upperHalfPlane := lt_of_le_of_ne hznonneg (Ne.symm hz0)
    have hpin : p ∈ cauchyImage φ := by
      refine ⟨z, hzh, ?_⟩
      exact (cauchyExtension_eq hφ.continuousOn hzh).symm.trans hzp
    exact ((cauchyImage_isOpen hφ hodd hzero hpos).frontier_eq ▸ hp).2 hpin
  refine Or.inl ⟨z.re, ?_⟩
  have hzeq : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz0]
  simpa only [hzeq] using hzp

private theorem verticalPath_tendsto (x : ℝ) :
    Tendsto (fun c : ℝ => (x : ℂ) + (c⁻¹ : ℝ) * Complex.I) atTop (𝓝 (x : ℂ)) := by
  have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  simpa using (tendsto_const_nhds.add (h.mul_const Complex.I))

private theorem verticalPath_mem (x : ℝ) :
    ∀ᶠ c : ℝ in atTop, (x : ℂ) + (c⁻¹ : ℝ) * Complex.I ∈ upperHalfPlane := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  simpa [upperHalfPlane] using inv_pos.2 hc

private theorem cauchy_vertical_extension_tendsto {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (x : ℝ) :
    Tendsto (fun c : ℝ => cauchy φ ((x : ℂ) + (c⁻¹ : ℝ) * Complex.I))
      atTop (𝓝 (cauchyExtension φ (x : ℂ))) := by
  obtain ⟨CY, hY⟩ := height_exists_holder (α := 1) hφ hodd hzero le_rfl
  have hlim : Tendsto (cauchy φ) (𝓝[upperHalfPlane] (x : ℂ))
      (𝓝 (cauchyExtension φ (x : ℂ))) := by
    simpa only [cauchyExtension_ofReal] using realCauchy_boundary_tendsto hY (by norm_num)
      (fun s hs => height_zero_of_one_le_abs φ hs) x
  exact hlim.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (verticalPath_tendsto x) (verticalPath_mem x))

/-- Every point of the actual real boundary curve belongs to the closure
of the open image, by the proved complex boundary limit. -/
theorem cauchyExtension_ofReal_mem_closure_image {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (x : ℝ) :
    cauchyExtension φ (x : ℂ) ∈ closure (cauchyImage φ) := by
  apply isClosed_closure.mem_of_tendsto (cauchy_vertical_extension_tendsto hφ hodd hzero x)
  filter_upwards [verticalPath_mem x] with c hc
  exact subset_closure ⟨_, hc, rfl⟩

/-- Univalence and continuity of the actual inverse prevent a real
boundary point from being mapped into the interior image. -/
theorem cauchyExtension_ofReal_not_mem_image {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) (x : ℝ) :
    cauchyExtension φ (x : ℂ) ∉ cauchyImage φ := by
  intro hp
  have hInvCont : ContinuousAt (cauchyInverse φ) (cauchyExtension φ (x : ℂ)) := by
    obtain ⟨z, hz, heq⟩ := hp
    rw [← heq]
    exact (cauchyInverse_hasDerivAt hφ hodd hzero hpos hz).continuousAt
  have hlim := hInvCont.tendsto.comp (cauchy_vertical_extension_tendsto hφ hodd hzero x)
  have hlim' : Tendsto (fun c : ℝ => (x : ℂ) + (c⁻¹ : ℝ) * Complex.I)
      atTop (𝓝 (cauchyInverse φ (cauchyExtension φ (x : ℂ)))) := by
    apply hlim.congr'
    filter_upwards [verticalPath_mem x] with c hc
    exact cauchyInverse_cauchy hφ hodd hzero hpos hc
  have heq : cauchyInverse φ (cauchyExtension φ (x : ℂ)) = (x : ℂ) :=
    tendsto_nhds_unique hlim' (verticalPath_tendsto x)
  have him := cauchyInverse_mem hp
  rw [heq] at him
  simp [upperHalfPlane] at him

theorem cauchyExtension_ofReal_mem_frontier {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) (x : ℝ) :
    cauchyExtension φ (x : ℂ) ∈ frontier (cauchyImage φ) := by
  rw [(cauchyImage_isOpen hφ hodd hzero hpos).frontier_eq]
  exact ⟨cauchyExtension_ofReal_mem_closure_image hφ hodd hzero x,
    cauchyExtension_ofReal_not_mem_image hφ hodd hzero hpos x⟩

/-- The image of infinity is a genuine frontier point. -/
theorem zero_mem_frontier_cauchyImage {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    (0 : ℂ) ∈ frontier (cauchyImage φ) := by
  have hnorm : Tendsto (fun t : ℝ => ‖(t : ℂ) * Complex.I‖) atTop atTop := by
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    exact tendsto_norm_atTop_atTop
  have hlim := cauchy_tendsto_zero hφ.continuousOn hnorm
  rw [(cauchyImage_isOpen hφ hodd hzero hpos).frontier_eq]
  constructor
  · apply isClosed_closure.mem_of_tendsto hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    apply subset_closure
    exact ⟨(t : ℂ) * Complex.I, by simpa [upperHalfPlane] using ht, rfl⟩
  · rintro ⟨z, hz, heq⟩
    have hi := cauchy_im_pos hφ.continuousOn hpos hz
    simp [heq] at hi

/-- Exact frontier identification from the actual continuous extension,
univalence, inverse regularity and decay. -/
theorem frontier_cauchyImage_eq {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    frontier (cauchyImage φ) =
      range (fun x : ℝ => cauchyExtension φ (x : ℂ)) ∪ {0} := by
  apply Subset.antisymm (frontier_cauchyImage_subset hφ hodd hzero hpos)
  rintro p (⟨x, rfl⟩ | hp)
  · exact cauchyExtension_ofReal_mem_frontier hφ hodd hzero hpos x
  · simpa only [mem_singleton_iff.1 hp] using zero_mem_frontier_cauchyImage hφ hodd hzero hpos

end Torsion.Spectral


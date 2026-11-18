module

public import Torsion.Proof.PaperExamplesField

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal ContDiff

namespace Torsion.PaperExamples

/-- The quadratic, extended by zero outside its positive ellipse, solves the
project's weak Dirichlet problem on the concrete Sobolev graph. -/
theorem ellipse_isWeakTorsion {A B : ℝ} (hB : 0 < B) (hBA : B ≤ A) :
    IsWeakTorsion (ellipse A B) (fun z => max (ellipseField A B z) 0)
      ((ellipse A B).indicator (ellipseGradient A B)) := by
  classical
  have hA := lt_of_lt_of_le hB hBA
  let D := ellipse A B
  let u : Plane → ℝ := fun z => max (ellipseField A B z) 0
  let g : Plane → Plane := D.indicator (ellipseGradient A B)
  have hop : IsOpen D := ellipse_isOpen hA hB
  have hb : Bornology.IsBounded D := ellipse_bounded A B
  have hf := ellipseField_contDiff A B
  have hc : Continuous u := hf.continuous.max continuous_const
  have hn {x : Plane} (hx : x ∈ D) : u =ᶠ[𝓝 x] ellipseField A B := by
    filter_upwards [hop.mem_nhds hx] with z hz
    exact max_eq_left ((ellipseField_pos_iff hA hB z).2 hz).le
  have hs : ContDiffOn ℝ ∞ u D :=
    fun x hx => (hf.contDiffAt.congr_of_eventuallyEq (hn hx)).contDiffWithinAt
  have hzero (x : Plane) (hx : x ∉ D) : u x = 0 :=
    max_eq_right (not_lt.mp (fun hp => hx ((ellipseField_pos_iff hA hB x).1 hp)))
  have hgrad (x : Plane) (hx : x ∈ D) : g x = gradient u x := by
    rw [(hn hx).gradient_eq, (ellipseField_hasGradientAt A B x).gradient]
    exact Set.indicator_of_mem hx _
  have hcompact {F : Type} [Zero F] {f : Plane → F}
      (h : ∀ x ∉ D, f x = 0) : HasCompactSupport f := by
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
    apply hb.closure.subset
    exact closure_mono (Function.support_subset_iff'.2 h)
  have hg0 (x : Plane) (hx : x ∉ D) : g x = 0 := Set.indicator_of_notMem hx _
  have hgLp : MemLp g 2 volume := by
    apply (hcompact hg0).memLp_of_bound
      ((ellipseGradient A B).continuous.aestronglyMeasurable.indicator hop.measurableSet)
      (shortAxisSlope A B)
    apply ae_of_all
    intro x
    by_cases hx : x ∈ D
    · simpa only [g, Set.indicator_of_mem hx] using ellipseGradient_le hB hBA hx
    · rw [hg0 x hx, norm_zero]
      unfold shortAxisSlope
      positivity
  have hmem := BoundaryAdmission.memH10_of_smooth_zero_extension hop hb hc hs hzero hgrad hg0
    (hc.memLp_of_hasCompactSupport (hcompact hzero)) hgLp
  apply isWeakTorsion_of_classical_poisson hop hb hmem hs
  · filter_upwards [ae_restrict_mem hop.measurableSet] with x hx
    exact hgrad x hx
  · intro x hx
    unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
    rw [(hn hx).gradient.fderiv_eq]
    exact ellipseField_laplacian hA hB x

/-- The actual weak-gradient objective equals the short-axis peak. -/
theorem ellipse_G (T : DirichletTheory) {A B : ℝ} (hB : 0 < B) (hBA : B ≤ A) :
    T.G (ellipseDomain (lt_of_lt_of_le hB hBA) hB) = ENNReal.ofReal (shortAxisSlope A B) := by
  have hA := lt_of_lt_of_le hB hBA
  let D := ellipseDomain hA hB
  have heq := (T.solution D).weakEquation.gradient_ae_eq (ellipse_isWeakTorsion hB hBA)
  have hind : ((ellipse A B).indicator (ellipseGradient A B)) =ᵐ[volume.restrict D.carrier]
      ellipseGradient A B := by
    filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with x hx
    exact Set.indicator_of_mem hx _
  change eLpNorm (T.solution D).weakGradient ∞ (volume.restrict D.carrier) = _
  rw [eLpNorm_congr_ae (heq.trans hind)]
  apply le_antisymm
  · rw [eLpNorm_exponent_top (ellipseGradient A B).continuous.aestronglyMeasurable]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with z hz
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (ellipseGradient_le hB hBA hz)
  · have htip : Complex.I ∈ closure (Metric.ball (0 : Plane) 1) := by
      rw [closure_ball _ one_ne_zero]
      simp
    have hp : axes A B Complex.I ∈ closure D.carrier :=
      (axes A B).continuous.continuousAt.continuousWithinAt.mem_closure_image htip
    have h := boundary_enorm_le_eLpNorm_top D.isOpen (ellipseGradient A B).continuous.continuousOn
      (ellipseGradient A B).continuous.continuousWithinAt hp
    simpa only [← ofReal_norm, ellipseGradient_tip hA hB] using h

/-- The normalized genuine weak objective depends only on the aspect ratio. -/
theorem normalized_ellipse_G (T : DirichletTheory) {A B : ℝ} (hB : 0 < B) (hBA : B ≤ A) :
    (T.G (ellipseDomain (lt_of_lt_of_le hB hBA) hB)).toReal /
      Real.sqrt (ellipseDomain (lt_of_lt_of_le hB hBA) hB).area = ellipseScore (A / B) := by
  have hA := lt_of_lt_of_le hB hBA
  have hs : 0 ≤ shortAxisSlope A B := by unfold shortAxisSlope; positivity
  rw [ellipse_G T hB hBA, ENNReal.toReal_ofReal hs, ellipse_area]
  simpa only [div_mul_cancel₀ A hB.ne'] using normalize_shortAxisSlope (div_pos hA hB) hB

/-- At area one, equality in the best-ellipse bound for the genuine weak
gradient occurs precisely at aspect ratio `√3`. -/
theorem ellipse_G_optimal_iff (T : DirichletTheory) {A B : ℝ} (hB : 0 < B) (hBA : B ≤ A)
    (ha : (ellipseDomain (lt_of_lt_of_le hB hBA) hB).area = 1) :
    (T.G (ellipseDomain (lt_of_lt_of_le hB hBA) hB)).toReal ≤ ellipseScore (Real.sqrt 3) ∧
      ((T.G (ellipseDomain (lt_of_lt_of_le hB hBA) hB)).toReal = ellipseScore (Real.sqrt 3)
        ↔ A / B = Real.sqrt 3) := by
  have he := normalized_ellipse_G T hB hBA
  rw [ha, Real.sqrt_one, div_one] at he
  rw [he]
  exact ellipseScore_optimal (div_pos (lt_of_lt_of_le hB hBA) hB)

/-- The area-one family with aspect ratio `r ≥ 1`, expressed on the actual
domain, realizes the score from Section 7. -/
theorem exists_area_one_ellipse_axes (T : DirichletTheory) {r : ℝ} (hr : 1 ≤ r) :
    ∃ B : ℝ, ∃ hB : 0 < B,
      let D := ellipseDomain (mul_pos (lt_of_lt_of_le zero_lt_one hr) hB) hB
      D.area = 1 ∧ T.G D = ENNReal.ofReal (ellipseScore r) := by
  have hr' : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let B := (Real.sqrt (Real.pi * r))⁻¹
  have hB : 0 < B := by dsimp [B]; positivity
  have hBA : B ≤ r * B := by simpa using mul_le_mul_of_nonneg_right hr hB.le
  let D := ellipseDomain (mul_pos hr' hB) hB
  have ha : D.area = 1 := by
    rw [ellipse_area]
    dsimp [B]
    have hsq := Real.sq_sqrt (mul_pos Real.pi_pos hr').le
    have hsr := Real.sqrt_pos.2 (mul_pos Real.pi_pos hr')
    field_simp
    nlinarith
  refine ⟨B, hB, ha, ?_⟩
  have hnum : Real.pi * (r * B) * B = 1 := (ellipse_area (mul_pos hr' hB) hB).symm.trans ha
  have he := normalize_shortAxisSlope hr' hB
  rw [hnum, Real.sqrt_one, div_one] at he
  exact (ellipse_G T hB hBA).trans (congrArg ENNReal.ofReal he)

theorem exists_area_one_ellipse (T : DirichletTheory) {r : ℝ} (hr : 1 ≤ r) :
    ∃ D : ConvexDomain, D.area = 1 ∧ T.G D = ENNReal.ofReal (ellipseScore r) := by
  obtain ⟨B, hB, ha, hg⟩ := exists_area_one_ellipse_axes T hr
  exact ⟨_, ha, hg⟩

/-- Every positive tolerance admits an area-one ellipse with smaller peak
gradient. -/
theorem exists_area_one_G_lt (T : DirichletTheory) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ConvexDomain, D.area = 1 ∧ T.G D < ENNReal.ofReal ε := by
  obtain ⟨r, hr, hlt⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (ellipseScore_tendsto_zero.eventually_lt_const hε)).exists
  obtain ⟨D, hD, hG⟩ := exists_area_one_ellipse T hr
  exact ⟨D, hD, hG.trans_lt (ENNReal.ofReal_lt_ofReal_iff hε |>.2 hlt)⟩

/-- The section's infimum, taken over the area-one convex domains. -/
theorem area_one_gradient_iInf (T : DirichletTheory) :
    (⨅ D : ConvexDomain, ⨅ _ : D.area = 1, T.G D) = 0 := by
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (ellipseScore r)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp ellipseScore_tendsto_zero
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  obtain ⟨D, ha, hg⟩ := exists_area_one_ellipse T hr
  rw [← hg]
  exact (iInf_le (fun E : ConvexDomain => ⨅ _ : E.area = 1, T.G E) D).trans
    (iInf_le _ ha)

/-- The area-one disk attains the stated concrete benchmark. -/
theorem area_one_disk_G (T : DirichletTheory) (R : ℝ) (hR : 0 < R)
    (ha : Real.pi * R * R = 1) :
    T.G (ellipseDomain hR hR) = ENNReal.ofReal (1 / (2 * Real.sqrt Real.pi)) := by
  have he := normalize_shortAxisSlope (r := 1) (by norm_num) hR
  rw [one_mul, ha, Real.sqrt_one, div_one, disk_score] at he
  exact (ellipse_G T hR le_rfl).trans (congrArg ENNReal.ofReal he)

end Torsion.PaperExamples

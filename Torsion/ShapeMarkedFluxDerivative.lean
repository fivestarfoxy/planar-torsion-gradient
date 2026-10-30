import Torsion.ShapeMaterialIdentification
import Torsion.ShapeMarkedPatch
import Torsion.MarkedFluxDifferentiation
import Torsion.LpParameterDerivative
import Torsion.RadialDeformation

/-!
# Actual marked torsion flux under a localized physical deformation

The genuine deformed weak solutions are identified with the differentiable
material family in H¹₀. On a fixed marked patch the deformation is the
identity, so their differences are actually weakly harmonic there. The
fixed reflection kernel then passes the strong material derivative to the
true inward flux. Differentiability of flux is a conclusion.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Torsion.Shape
open HilbertDirichlet

private theorem weakHarmonic_of_gradient_eqOn {U : Set Plane}
    {u v : Plane → ℝ} {g h : Plane → Plane}
    (hw : IsWeakHarmonicOn U u g) (hd : HasDistributionalGradient v h)
    (heq : EqOn h g U) : IsWeakHarmonicOn U v h := by
  refine ⟨hd, ?_⟩
  intro ψ hψ
  rw [← hw.2 ψ hψ]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  change inner (𝕜 := ℝ) (h z) (gradient ψ z) = inner (𝕜 := ℝ) (g z) (gradient ψ z)
  by_cases hz : z ∈ U
  · rw [heq hz]
  · rw [gradient_eq_zero_of_not_mem_tsupport (fun h => hz (hψ.2.2 h))]
    simp

/-- Every smooth compact displacement supported above the flat boundary
and zero near the marked point gives an actual differentiable marked
torsion flux. Its derivative is the fixed-kernel action of the constructed
strong material derivative, not an assumed shape derivative. -/
theorem exists_torsionFlux_deformation_hasDerivAt {D : Set Plane} (hD : IsMarked D)
    {V : Plane → Plane} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVU : tsupport V ⊆ upperHalfPlane)
    (hzero : V =ᶠ[𝓝 (0 : Plane)] (fun _ => 0)) :
    ∃ r : ℝ, 0 < r ∧
      upperHalfPlane ∩ Metric.ball (0 : Plane) (4 * r) ⊆ D ∧
      (∀ z ∈ Metric.ball (0 : Plane) (4 * r), V =ᶠ[𝓝 z] (fun _ => 0)) ∧
      HasDerivAt
      (fun t : ℝ => torsionFlux (deformation V t '' D))
      (markedGradientFlux r
        (gradientMap D (materialDerivative D hD.1.measurableSet hD.2.1 hV hVc))) 0 := by
  obtain ⟨r, hr, hVpatch, hpatch⟩ := exists_fixed_marked_patch_with_zero hD hVU hzero
  obtain ⟨δ, hδ, hidentify⟩ := exists_materialSolution_identification
    D hD.1.measurableSet hD.2.1 hV hVc
  let J := {t : ℝ // |t| < δ}
  have hzeroδ : |(0 : ℝ)| < δ := by simpa using hδ
  let j₀ : J := ⟨0, hzeroδ⟩
  choose e heq heinv hid using (fun t : J => hidentify t.1 t.2)
  have hmarked (t : J) : IsMarked (deformation V t.1 '' D) := by
    simpa only [← heq t] using (hpatch t.1 (e t) (heq t)).1
  choose u g s hu hs hc hq using (fun t : J => torsionFlux_spec (hmarked t))
  have hpulled (t : J) : ∃ hm : MemH10 D ((u t) ∘ (e t))
      (gradientPullback (e t) (g t)),
      ofMemH10 hm = materialSolution D hD.1.measurableSet hD.2.1 hV hVc t.1 :=
    hid t (u t) (g t) (hu t)
  choose hm hclass using hpulled
  let UJ (t : J) : Plane → ℝ := (u t) ∘ (e t)
  let GJ (t : J) : Plane → Plane := gradientPullback (e t) (g t)
  have hmem (t : J) : MemH10 upperHalfPlane (UJ t) (GJ t) :=
    (hm t).mono hD.2.2.1
  have hpoint (t : J) (z : Plane) (hz : z ∈ Metric.ball 0 (4 * r)) :
      UJ t z = u t z ∧ GJ t z = g t z := by
    rcases (hpatch t.1 (e t) (heq t)).2.2.2 z hz with
      ⟨hneigh, hsymm, hderiv, hgrad, hval⟩
    exact ⟨hval (u t), hgrad (g t)⟩
  have hflux (t : J) : HasMarkedFlux (UJ t) (torsionFlux (deformation V t.1 '' D)) := by
    apply (hq t).congr'
    filter_upwards [eventually_vertical_mem_halfBall (r := 4 * r) (by positivity)] with y hy
    rw [(hpoint t _ hy.2).1]
  have hcont (t : J) : ∃ a : ℝ, 0 < a ∧
      ContinuousOn (UJ t) (upperHalfPlane ∩ Metric.ball 0 a) := by
    refine ⟨min (s t) (4 * r), lt_min (hs t) (by positivity), ?_⟩
    apply ((hc t).mono (inter_subset_inter_right _
      (Metric.ball_subset_ball (min_le_left _ _)))).congr
    intro z hz
    exact (hpoint t z (Metric.ball_subset_ball (min_le_right _ _) hz.2)).1
  have hcommon (t : J) : upperHalfPlane ∩ Metric.ball 0 (4 * r) ⊆
      deformation V t.1 '' D := by
    simpa only [← heq t] using (hpatch t.1 (e t) (heq t)).2.2.1
  have hweak (t : J) : IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 (4 * r))
      (fun z => UJ t z - UJ j₀ z) (fun z => GJ t z - GJ j₀ z) := by
    apply weakHarmonic_of_gradient_eqOn
      ((hu t).difference_weakHarmonicOn (hu j₀) (hcommon t) (hcommon j₀))
      ((hmem t).sub (hmem j₀)).distributionalGradient
    intro z hz
    change GJ t z - GJ j₀ z = g t z - g j₀ z
    rw [(hpoint t z hz.2).2, (hpoint j₀ z hz.2).2]
  let j (t : ℝ) : J := if ht : |t| < δ then ⟨t, ht⟩ else j₀
  have hj (t : ℝ) (ht : |t| < δ) : j t = ⟨t, ht⟩ := dif_pos ht
  have hj₀ : j 0 = j₀ := by simp only [j, dif_pos hzeroδ]; rfl
  let U (t : ℝ) : Plane → ℝ := UJ (j t)
  let G (t : ℝ) : Plane → Plane := GJ (j t)
  let F (t : ℝ) := gradientMap D (materialSolution D hD.1.measurableSet hD.2.1 hV hVc t)
  let F' := gradientMap D (materialDerivative D hD.1.measurableSet hD.2.1 hV hVc)
  have hGclass (t : ℝ) (ht : |t| < δ) : G t =ᵐ[volume] (F t : Plane → Plane) := by
    have hgrad : (gradientMap D (ofMemH10 (hm ⟨t, ht⟩)) : Plane → Plane) =ᵐ[volume]
        gradientPullback (e ⟨t, ht⟩) (g ⟨t, ht⟩) := by
      simpa only [gradientMap_ofMemH10] using (hm ⟨t, ht⟩).2.1.coeFn_toLp
    rw [hclass] at hgrad
    simpa only [G, hj t ht, GJ, F] using hgrad.symm
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| < δ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
  have hgradient : HasDerivAt F F' 0 :=
    materialGradient_hasDerivAt_zero D hD.1.measurableSet hD.2.1 hV hVc
  have hlim := lp_derivative_eLpNorm_quotient_tendsto_of_ae_eq hgradient
    ((hsmall.filter_mono nhdsWithin_le_nhds).mono fun t ht => hGclass t ht)
    (hGclass 0 hzeroδ) (Eventually.of_forall fun _ => rfl)
  obtain ⟨a₀, ha₀, hc₀⟩ := hcont j₀
  have hdata : ∀ᶠ t in 𝓝[(univ : Set ℝ) \ {0}] 0,
      MemH10 upperHalfPlane (U t) (G t) ∧
      IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 (4 * r))
        (fun z => U t z - U 0 z) (fun z => G t z - G 0 z) ∧
      ∃ a : ℝ, 0 < a ∧ ContinuousOn (U t) (upperHalfPlane ∩ Metric.ball 0 a) ∧
        HasMarkedFlux (U t) (torsionFlux (deformation V t '' D)) := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds] with t ht
    obtain ⟨a, ha, hca⟩ := hcont (j t)
    refine ⟨hmem (j t), ?_, a, ha, hca, ?_⟩
    · simpa only [U, G, hj₀] using hweak (j t)
    · simpa only [U, hj t ht] using hflux (j t)
  refine ⟨r, hr, (hpatch j₀.1 (e j₀) (heq j₀)).2.1, hVpatch,
    hasDerivWithinAt_univ.mp ?_⟩
  have hq₀ : HasMarkedFlux (U 0) (torsionFlux (deformation V 0 '' D)) := by
    simpa only [U, hj₀] using hflux j₀
  exact markedFlux_hasDerivWithinAt_of_eLpNorm_gradient_quotient hr ha₀
    (hmem (j 0)) (by simpa only [U, hj₀] using hc₀) hq₀ (Lp.memLp F') hdata
    (by simpa only [F', ← Set.compl_eq_univ_diff] using hlim)

/-- A compact smooth angular perturbation of any positive continuous radial
profile has an actual two-sided marked torsion-flux derivative. The physical
field realizing that perturbation and its strong material derivative are
both constructed; no differentiability or flux-variation assumption occurs. -/
theorem exists_local_radialFlux_hasDerivAt {R f : ℝ → ℝ}
    (hR : ContinuousOn R (Icc 0 Real.pi))
    (hRpos : ∀ θ ∈ Icc 0 Real.pi, 0 < R θ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ Ioo 0 Real.pi) :
    ∃ (V : Plane → Plane) (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (r : ℝ),
      tsupport V ⊆ upperHalfPlane ∧ 0 < r ∧
      (∀ θ ∈ Ioo 0 Real.pi,
        V ((R θ : Plane) * Complex.exp ((θ : Plane) * Complex.I)) =
          (f θ : ℝ) • Complex.exp ((θ : Plane) * Complex.I)) ∧
      upperHalfPlane ∩ Metric.ball (0 : Plane) (4 * r) ⊆ radialDomain R ∧
      (∀ z ∈ Metric.ball (0 : Plane) (4 * r), V =ᶠ[𝓝 z] (fun _ => 0)) ∧
      HasDerivAt (fun t : ℝ => torsionFlux (radialDomain (fun θ => R θ + t * f θ)))
        (markedGradientFlux r (gradientMap (radialDomain R)
          (materialDerivative (radialDomain R)
            (RadialGeometry.radialDomain_isOpen hR).measurableSet
            (RadialGeometry.radialDomain_bounded hR) hV hVc))) 0 := by
  obtain ⟨V, δ, hV, hVc, hVU, hδ, hzero, hboundary, hchange⟩ :=
    exists_local_radial_deformation hR hRpos hf hfc hfU
  have hD := RadialGeometry.radialDomain_isMarked hR hRpos
  obtain ⟨r, hr, hhalf, hVpatch, hderiv⟩ := exists_torsionFlux_deformation_hasDerivAt
    hD hV hVc hVU (hzero 0)
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| < δ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
  have heq : (fun t : ℝ => torsionFlux (radialDomain (fun θ => R θ + t * f θ))) =ᶠ[𝓝 0]
      (fun t : ℝ => torsionFlux (deformation V t '' radialDomain R)) := by
    filter_upwards [hsmall] with t ht
    obtain ⟨hpos, e, heq, he, heinv, himage⟩ := hchange t ht
    rw [show deformation V t '' radialDomain R = radialDomain (fun θ => R θ + t * f θ)
      from by simpa only [heq] using himage]
  refine ⟨V, hV, hVc, r, hVU, hr, hboundary, hhalf, hVpatch, ?_⟩
  exact hderiv.congr_of_eventuallyEq heq

end Torsion.Shape

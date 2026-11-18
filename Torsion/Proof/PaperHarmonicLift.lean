module

public import Torsion.Proof.PaperPoissonData
public import Torsion.ConvexTorsionContinuity
public import Torsion.ClassicalWeakLaplacian

@[expose] public section

/-! # Smooth data lifted to a weak harmonic function, with a boundary barrier -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace Torsion
open WeakHarmonicRegularity

theorem continuous_planarLaplacian_of_contDiff {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b) :
    Continuous (planarLaplacian b) := by
  have hg := contDiffOn_univ.mp (contDiffOn_gradient_of_isOpen hb.contDiffOn isOpen_univ)
  have hc (e : Plane) : Continuous (fun z => fderiv ℝ (gradient b) z e) :=
    (ContinuousLinearMap.apply ℝ Plane e).continuous.comp (hg.continuous_fderiv (by simp))
  exact (Complex.continuous_re.comp (hc 1)).add (Complex.continuous_im.comp (hc Complex.I))

/-- The lifted function is weakly harmonic, differs from the boundary data by
an actual zero-trace function, and is controlled up to the boundary by a
continuous barrier which vanishes off the domain. -/
theorem exists_weak_harmonic_extension (D : ConvexDomain) {b : Plane → ℝ} (hb : IsTest univ b) :
    ∃ (H : Plane → ℝ) (G : Plane → Plane) (B : Plane → ℝ),
      MemH10 univ H G ∧ IsWeakHarmonicOn D.carrier H G ∧
      MemH10 D.carrier (fun x => H x - b x) (fun x => G x - gradient b x) ∧
      Continuous B ∧ (∀ x ∉ D.carrier, B x = 0) ∧
      (∀ᵐ z ∂volume.restrict D.carrier, |H z - b z| ≤ B z) := by
  obtain ⟨η, hη, hηone⟩ := exists_test_eq_one_near_compact isOpen_univ
    D.bounded.isCompact_closure (subset_univ _)
  have h1 (z) (hz : z ∈ D.carrier) : η z = 1 :=
    (hηone.filter_mono (nhds_le_nhdsSet (subset_closure hz))).self_of_nhds
  let f (z : Plane) := planarLaplacian b z * η z
  have hc := continuous_planarLaplacian_of_contDiff hb.1
  have hf : MemLp f 2 volume :=
    (hc.mul hη.1.continuous).memLp_of_hasCompactSupport (hη.2.1.mul_left)
  have hfeq (z) (hz : z ∈ D.carrier) : f z = planarLaplacian b z := by simp [f, h1 _ hz]
  obtain ⟨w, g, hw⟩ := exists_l2Poisson D hf
  let H (z : Plane) := w z + b z
  let G (z : Plane) := g z + gradient b z
  have hH : MemH10 univ H G := (hw.1.mono (subset_univ _)).add hb.memH10
  have hharm : IsWeakHarmonicOn D.carrier H G := by
    refine ⟨hH.distributionalGradient, ?_⟩
    intro ψ hψ
    have heq : (∫ z, f z * ψ z) = ∫ z, planarLaplacian b z * ψ z := by
      apply integral_congr_ae (Eventually.of_forall ?_)
      intro z
      by_cases hz : z ∈ D.carrier
      · rw [hfeq _ hz]
      · have hz' : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hψ.2.2 h))
        simp [hz']
    simp only [G, inner_add_left]
    rw [integral_add (integrable_real_inner_of_memLp_two hw.1.2.1 (hψ.memLp_gradient (p := 2)))
      (integrable_real_inner_of_memLp_two (hb.memLp_gradient (p := 2)) (hψ.memLp_gradient (p := 2))),
      hw.2 _ _ hψ.memH10, heq, classical_laplacian_smooth_test_equation D.isOpen hb.1.contDiffOn hψ,
      add_neg_cancel]
  let S := HilbertDirichlet.solution D
  obtain ⟨T, hTc, _, hTz, _, hST, _⟩ := S.weakEquation.exists_continuous_smooth_representative
  have hT := S.weakEquation.l2Poisson_of_one_on h1
  obtain ⟨m, hm, hm'⟩ := D.bounded.isCompact_closure.exists_isMaxOn D.nonempty.closure hc.abs.continuousOn
  let M := |planarLaplacian b m|
  have hbnd (z) (hz : z ∈ D.carrier) : |f z| ≤ M := by rw [hfeq z hz]; exact hm' (subset_closure hz)
  have hau : ∀ᵐ z ∂volume, w z ≤ M • S.value z :=
    hw.le_of_source_le (hT.const_smul M) hf ((hη.memLp_value (p := 2)).const_mul M) fun z hz => by
      rw [h1 z hz, mul_one]
      exact (le_abs_self _).trans (hbnd z hz)
  have hal : ∀ᵐ z ∂volume, (-M) • S.value z ≤ w z :=
    (hT.const_smul (-M)).le_of_source_le hw ((hη.memLp_value (p := 2)).const_mul (-M)) hf fun z hz => by
      rw [h1 z hz, mul_one]
      exact (abs_le.mp (hbnd z hz)).1
  refine ⟨H, G, fun z => M * T z, hH, hharm, ?_, continuous_const.mul hTc, ?_, ?_⟩
  · simpa only [H, G, add_sub_cancel_right] using hw.1
  · intro z hz
    simp [hTz z hz]
  · filter_upwards [ae_restrict_of_ae hau, ae_restrict_of_ae hal, hST] with z hu hl hTz
    rw [show H z - b z = w z by simp [H]]
    simp only [smul_eq_mul, neg_mul, hTz] at hu hl
    exact abs_le.mpr ⟨hl, hu⟩

/-- Green's identity for the lifting problem, prior to identifying the boundary
functional with the normal derivative and surface measure. -/
theorem weak_harmonic_integral_eq_torsion_flux (D : ConvexDomain)
    {u H b : Plane → ℝ} {g G : Plane → Plane}
    (hu : IsWeakTorsion D.carrier u g) (hb : IsTest univ b)
    (hH : MemH10 univ H G) (hh : IsWeakHarmonicOn D.carrier H G)
    (htrace : MemH10 D.carrier (fun z => H z - b z) (fun z => G z - gradient b z)) :
    (∫ z in D.carrier, H z) = (∫ z in D.carrier, b z) -
      ∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (gradient b z) := by
  let : IsFiniteMeasure (volume.restrict D.carrier) := isFiniteMeasure_restrict.mpr D.bounded.measure_lt_top.ne
  have hg := hh.sobolev_test_equation hH.2.1 hu.1
  have ha : (∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (G z)) = 0 := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero, ← hg]
    · exact integral_congr_ae (Eventually.of_forall fun z => real_inner_comm _ _)
    · filter_upwards [(ae_restrict_iff' D.isOpen.measurableSet.compl).mp hu.1.gradient_ae_zero_off] with z hz hD
      simp [show g z = 0 from hz hD]
  have he := hu.2 _ _ htrace
  simp only [inner_sub_right] at he
  rw [integral_sub (integrable_real_inner_of_memLp_two hu.1.2.1 hH.2.1).integrableOn
    (integrable_real_inner_of_memLp_two hu.1.2.1 hb.memH10.2.1).integrableOn, ha,
    integral_sub ((hH.1.restrict D.carrier).integrable (by norm_num)) ((hb.memH10.1.restrict D.carrier).integrable (by norm_num))] at he
  linarith

end Torsion

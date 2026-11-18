module

public import Torsion.Proof.PaperArclengthBlowup
public import Torsion.Proof.PaperBoundaryBlowup
public import Torsion.Proof.PaperBoundaryBump
public import Torsion.Proof.PaperHalfPlaneBumpFlux
public import Torsion.Proof.PaperWeakBoundaryUpper
public import Torsion.Proof.PaperWeakFluxBlowup
public import Torsion.Proof.PaperWeakHermiteSharpness

@[expose] public section

/-! # The sharp Hermite–Hadamard coefficient for a smooth convex frame

The coefficient is the original weak torsion-gradient norm. At a maximizing
boundary mark a contracting physical bump has weak torsion flux tending,
after scaling, to this norm times its limiting arclength. Harmonic extensions
and uniform approximation on the closed body turn this ratio into sharpness
for actual smooth subharmonic functions. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion.HermiteHadamard
open WeakHarmonicRegularity

/-- Every valid coefficient, even when validity is required only on compactly
supported smooth harmonic functions, dominates the true weak gradient norm. -/
theorem harmonic_coefficient_lower (T : DirichletTheory) (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ))
    {C : ℝ} (hC : BoundsHarmonicTests D (curveArclength (radialFrameCurve c R) (-Real.pi) Real.pi) C) :
    (T.G D).toReal ≤ C := by
  let γ := radialFrameCurve c R
  let σ := curveArclength γ (-Real.pi) Real.pi
  have hγ := radialFrameCurve_contDiff c hR
  have hσ : IsFiniteMeasure σ := curveArclength_finite hγ _ _
  have hK : ∀ᵐ z ∂σ, z ∈ frontier D.carrier := curveArclength_ae_mem hγ.continuous
    isClosed_frontier.measurableSet (radialFrameCurve_mem_frontier D c R hR hpos hmem)
  obtain ⟨s⟩ := T.exists_maximizingNormalSequence D
  let B := radialKernelRaw 1
  have hB : IsTest univ B :=
    ⟨radialKernelRaw_contDiff 1, radialKernelRaw_hasCompactSupport (by norm_num), subset_univ _⟩
  let b := boundaryBump B s.point
  let I := 2 * ∫ t in Ioi (0 : ℝ), boundaryBumpProfile t
  have hflux := weakBoundaryFlux_bump_tendsto D s.weak.1 s.continuous hB s.point s.normal
    (T.G D).toReal s.blowup_tendsto s.blowup_abs_le
  have hFL : (∫ z : Plane, (T.G D).toReal * max 0 (inner (𝕜 := ℝ) s.normal z) * planarLaplacian B z) =
      (T.G D).toReal * I := by
    simp_rw [mul_assoc]
    rw [integral_const_mul, halfPlaneRamp_integral_laplacian s.normal s.unit hB]
    congr 1
    exact boundaryBumpProfile_line (v := Complex.I * s.normal) (by simp [s.unit])
  rw [hFL] at hflux
  apply hC.coefficient_ge_of_flux_limits hK s.weak b (fun r hr => boundaryBump_isTest hB s.point hr)
    (fun r _ z => radialKernelRaw_nonneg _ _) boundaryBumpProfile_line_pos
  · simpa only [div_eq_inv_mul, weakBoundaryFlux, b] using hflux
  · exact frontier_arclength_radialKernelRaw D c R hR hpos hend hmem s.point_mem

/-- Every valid coefficient, even when validity is required only on compactly
supported smooth subharmonic functions, dominates the true weak gradient norm. -/
theorem sharp_coefficient_lower (T : DirichletTheory) (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ))
    {C : ℝ} (hC : BoundsSmoothTests D (curveArclength (radialFrameCurve c R) (-Real.pi) Real.pi) C) :
    (T.G D).toReal ≤ C :=
  harmonic_coefficient_lower T D c R hR hpos hend hmem hC.toHarmonic

/-- Manuscript §8. The supremal weak torsion-gradient norm is the exact
coefficient for the volume integral versus genuine arclength of nonnegative
boundary traces of smooth subharmonic tests. -/
theorem smooth_radial_hermiteHadamard_iff (T : DirichletTheory) (D : ConvexDomain)
    (c : Plane) (R : ℝ → ℝ) (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ)
    (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ)) (C : ℝ) :
    (∀ f : Plane → ℝ, ContDiff ℝ ∞ f → (∀ z ∈ D.carrier, 0 ≤ planarLaplacian f z) →
      (∀ z ∈ frontier D.carrier, 0 ≤ f z) → (∫ z in D.carrier, f z) ≤
        C * ∫ z, f z ∂curveArclength (radialFrameCurve c R) (-Real.pi) Real.pi) ↔
      (T.G D).toReal ≤ C := by
  constructor
  · intro h
    exact sharp_coefficient_lower T D c R hR hpos hend hmem (fun f hf => h f hf.1)
  · intro hC f hf hsub hbd
    have h := smoothRadial_weak_hermiteHadamard T D c R hR hpos hend hmem hf hsub hbd
    let γ := radialFrameCurve c R
    let σ := curveArclength γ (-Real.pi) Real.pi
    have hγ := radialFrameCurve_contDiff c hR
    have hsupp : ∀ᵐ z ∂σ, z ∈ frontier D.carrier := curveArclength_ae_mem hγ.continuous
      isClosed_frontier.measurableSet (radialFrameCurve_mem_frontier D c R hR hpos hmem)
    have hposI : 0 ≤ ∫ z, f z ∂σ := integral_nonneg_of_ae (hsupp.mono fun x hx => hbd x hx)
    have heq : (∫ z, f z ∂σ) =
        ∫ θ in (-Real.pi)..Real.pi, f (γ θ) * ‖deriv γ θ‖ := by
      rw [integral_curveArclength hγ _ _ hf.continuous.measurable,
        intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _
      exact mul_comm _ _
    rw [← heq] at h
    exact h.trans (mul_le_mul_of_nonneg_right hC hposI)

/-- Smooth compact functions harmonic in the original domain realize volumes
arbitrarily close to the sharp coefficient with exactly one unit of boundary
arclength mass and nonnegative boundary trace. -/
theorem exists_normalized_near_extremal_harmonic_test (T : DirichletTheory) (D : ConvexDomain)
    (c : Plane) (R : ℝ → ℝ) (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ)
    (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Plane → ℝ, IsTest univ f ∧ (∀ x ∈ D.carrier, planarLaplacian f x = 0) ∧
      (∀ x ∈ frontier D.carrier, 0 ≤ f x) ∧
      (∫ x, f x ∂curveArclength (radialFrameCurve c R) (-Real.pi) Real.pi) = 1 ∧
      (T.G D).toReal - ε < (∫ x in D.carrier, f x) ∧ (∫ x in D.carrier, f x) ≤ (T.G D).toReal := by
  let σ := curveArclength (radialFrameCurve c R) (-Real.pi) Real.pi
  let G := (T.G D).toReal
  have hbad : ¬ BoundsHarmonicTests D σ (G - ε) := fun h =>
    (sub_lt_self G hε).not_ge (harmonic_coefficient_lower T D c R hR hpos hend hmem h)
  unfold BoundsHarmonicTests at hbad
  push Not at hbad
  obtain ⟨v, hv, hLap, htrace, hnear⟩ := hbad
  let B := ∫ x, v x ∂σ
  have hub := (smooth_radial_hermiteHadamard_iff T D c R hR hpos hend hmem G).mpr le_rfl
    v hv.1 (fun x hx => (hLap x hx).ge) htrace
  change (G - ε) * B < (∫ x in D.carrier, v x) at hnear
  change (∫ x in D.carrier, v x) ≤ G * B at hub
  have hB : 0 < B := by nlinarith
  let k := B⁻¹
  have hk : 0 < k := inv_pos.mpr hB
  let _ : Invertible k := invertibleOfNonzero hk.ne'
  let f := k • v
  have hg : gradient f = k • gradient v := by
    ext x : 1
    simp only [f, gradient, fderiv_const_smul_of_invertible, map_smul, Pi.smul_apply]
  have hL (x : Plane) : planarLaplacian f x = k * planarLaplacian v x := by
    rw [planarLaplacian, planarDivergence, hg, fderiv_const_smul_of_invertible k]
    simp only [planarLaplacian, planarDivergence, smul_apply, Complex.real_smul, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    ring
  have hnorm : k * B = 1 := inv_mul_cancel₀ hB.ne'
  refine ⟨f, hv.const_smul k, fun x hx => by rw [hL, hLap x hx, mul_zero],
    fun x hx => mul_nonneg hk.le (htrace x hx), ?_, ?_, ?_⟩
  · change (∫ x, k * v x ∂σ) = 1
    rwa [integral_const_mul]
  · change G - ε < ∫ x in D.carrier, k * v x
    rw [integral_const_mul]
    have h := mul_lt_mul_of_pos_left hnear hk
    calc
      G - ε = k * ((G - ε) * B) := by linear_combination -(G - ε) * hnorm
      _ < _ := h
  · change (∫ x in D.carrier, k * v x) ≤ G
    rw [integral_const_mul]
    calc
      _ ≤ k * (G * B) := mul_le_mul_of_nonneg_left hub hk.le
      _ = G := by linear_combination G * hnorm

end Torsion.HermiteHadamard

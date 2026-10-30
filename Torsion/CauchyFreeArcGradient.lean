import Torsion.CauchyFreeArcInverse

/-! # Full local smoothness of the physical torsion gradient at the free arc -/

noncomputable section
open Set Filter
open scoped Topology NNReal ContDiff

namespace Torsion.Spectral

/-- The actual spectral torsion gradient has a genuine C∞ extension to a
full physical neighborhood of every point of the open free arc. This is
derived from spectral analytic continuation and the actual inverse. -/
theorem IsRestrictedEigenfunction.exists_smooth_gradient_at_freeArc
    {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ) (ha : 0 < a)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ s ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ s = a * height φ s - b)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ∃ G : Plane → Plane,
      ContDiffAt ℝ ∞ G (cauchyExtension φ (t : Plane)) ∧
      G =ᶠ[𝓝[cauchyImage φ] (cauchyExtension φ (t : Plane))]
        gradient (physicalCandidate φ) := by
  obtain ⟨r, A, K, hr, hAd, hA, hK, hKt, hKeq⟩ :=
    hEig.exists_smooth_chart_at_freeArc ha hφ hα0 hα1 hodd hzero hpos hlinear ht
  have hDA : ContDiffAt ℂ ∞ (deriv A) (t : Plane) :=
    ((hAd.analyticOnNhd Metric.isOpen_ball).deriv (t : Plane) (Metric.mem_ball_self hr)).contDiffAt
  have hDAK : ContDiffAt ℂ ∞ (fun w => deriv A (K w)) (cauchyExtension φ (t : Plane)) := by
    have hDA' : ContDiffAt ℂ ∞ (deriv A) (K (cauchyExtension φ (t : Plane))) := by
      simpa only [hKt] using hDA
    exact hDA'.comp _ hK
  let B : Plane → Plane := fun w => ComplexIdentity.physicalDerivative a b (deriv A (K w))
  let G : Plane → Plane := fun w => Complex.I * star (B w) - (w.im : Plane) * Complex.I
  have hB : ContDiffAt ℝ ∞ B (cauchyExtension φ (t : Plane)) :=
    contDiffAt_const.sub ((hDAK.restrict_scalars ℝ).div_const _)
  have hG : ContDiffAt ℝ ∞ G (cauchyExtension φ (t : Plane)) := by
    exact (contDiffAt_const.mul (Complex.conjCLE.contDiff.contDiffAt.comp _ hB)).sub
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ Complex.imCLM.contDiff.contDiffAt).mul
        contDiffAt_const)
  refine ⟨G, hG, ?_⟩
  have hinv := cauchyInverse_boundary_tendsto hφ hα0 hα1 hodd hzero hpos t
  filter_upwards [hinv.eventually (Metric.ball_mem_nhds _ hr), hKeq,
    self_mem_nhdsWithin] with w hw hKw hwD
  have hAeq : A =ᶠ[𝓝 (cauchyInverse φ w)] cauchy φ := by
    filter_upwards [(Metric.isOpen_ball.inter
      (isOpen_lt continuous_const Complex.continuous_im)).mem_nhds
        ⟨hw, cauchyInverse_mem hwD⟩] with z hz
    exact hA hz
  have hgrad := gradient_physicalCandidate_cauchy ha.ne' hφ hα0 hα1 hodd hzero hpos
    hlinear (cauchyInverse_mem hwD)
  rw [cauchy_cauchyInverse hwD] at hgrad
  dsimp only [G, B]
  rw [hKw, hAeq.deriv_eq]
  exact hgrad.symm

end Torsion.Spectral

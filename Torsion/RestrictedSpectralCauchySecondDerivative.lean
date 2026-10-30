import Torsion.RestrictedSpectralQuadraticZero

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- The actual weak spectral equation fixes the real second derivative of
any constructed holomorphic height extension at each interior real point. -/
theorem IsRestrictedEigenfunction.exists_height_Cauchy_extension_secondDerivative_re
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : ℂ → ℂ,
      DifferentiableOn ℂ A (Metric.ball (x : ℂ) r) ∧
      EqOn A (realCauchyExtension (height f))
        (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (deriv (deriv A) (x : ℂ)).re = a * regularEigenfunction f x := by
  obtain ⟨r, hr, A, hAd, hAeq⟩ := hf.exists_height_Cauchy_extension_of_odd hodd x hx
  have hAa := hAd.analyticOnNhd Metric.isOpen_ball
  obtain ⟨b, hb⟩ := hf.height_Cauchy_boundary_hasDerivAt hodd
  have hReD (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) (htr : (t : ℂ) ∈ Metric.ball (x : ℂ) r) :
      (deriv A (t : ℂ)).re = -a * height f t + b := by
    have hAt := hAd.differentiableAt (Metric.isOpen_ball.mem_nhds htr)
    have hd : HasDerivAt (fun s : ℝ => (A (s : ℂ)).re) ((deriv A (t : ℂ)).re) t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hAt.hasDerivAt.comp_ofReal
    have heq : (fun s : ℝ => (A (s : ℂ)).re) =ᶠ[𝓝 t] realCauchyBoundaryRe (height f) := by
      filter_upwards [(Metric.isOpen_ball.preimage Complex.continuous_ofReal).mem_nhds htr] with s hs
      rw [hAeq ⟨hs, by simp⟩, realCauchyExtension_ofReal]
      simp
    exact hd.unique ((hb t ht).congr_of_eventuallyEq heq)
  have hxball : (x : ℂ) ∈ Metric.ball (x : ℂ) r := Metric.mem_ball_self hr
  have hDAt := (hAa.deriv (x : ℂ) hxball).differentiableAt
  have hDD : HasDerivAt (fun t : ℝ => (deriv A (t : ℂ)).re)
      ((deriv (deriv A) (x : ℂ)).re) x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hDAt.hasDerivAt.comp_ofReal
  have hY : HasDerivAt (height f) (-regularEigenfunction f x) x := by
    rw [regularEigenfunction, if_pos (abs_lt.2 hx), neg_neg]
    exact (hf.height_analyticAt_of_odd hodd x hx).differentiableAt.hasDerivAt
  have hR : HasDerivAt (fun t : ℝ => -a * height f t + b) (a * regularEigenfunction f x) x := by
    convert (hY.const_mul (-a)).add_const b using 1
    ring
  have heqD : (fun t : ℝ => (deriv A (t : ℂ)).re) =ᶠ[𝓝 x]
      (fun t : ℝ => -a * height f t + b) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx,
      (Metric.isOpen_ball.preimage Complex.continuous_ofReal).mem_nhds hxball] with t ht htr
    exact hReD t ht htr
  exact ⟨r, hr, A, hAd, hAeq, hDD.unique (hR.congr_of_eventuallyEq heqD)⟩

end Torsion.Spectral

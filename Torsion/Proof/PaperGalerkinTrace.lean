module

public import Torsion.Proof.PaperGalerkinModes

@[expose] public section

/-! # The Cauchy trace of the finite Galerkin profile -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Torsion.Galerkin
open Spectral Polynomial.Chebyshev

private theorem mode_sine_global (j : ℤ) (hj : 0 < j) (x : ℝ) :
    trialMode j.toNat x = Real.sin ((j : ℝ) * Real.arccos x) := by
  by_cases hx : |x| ≤ 1
  · rw [trialMode_sine _ hx, ← Int.cast_natCast, Int.toNat_of_nonneg hj.le]
  · rw [trialMode_zero_exterior _ x (le_of_not_ge hx)]
    rcases le_abs.mp (le_of_not_ge hx) with h | h
    · rw [Real.arccos_of_one_le h]
      simp
    · rw [Real.arccos_of_le_neg_one (by linarith), Real.sin_int_mul_pi]

private theorem subtracted_modes_sum (s : Finset ℤ) (d : ℤ → ℝ) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) :
    subtractedRealCauchy (fun x => ∑ j ∈ s, d j * trialMode j.toNat x) R z =
      ∑ j ∈ s, d j * subtractedRealCauchy (trialMode j.toNat) R z := by
  let g (j : ℤ) (t : ℝ) := t / (t ^ 2 + z.im ^ 2) *
    (trialMode j.toNat (z.re + t) - trialMode j.toNat z.re)
  have hint (j : ℤ) : IntegrableOn (g j) (Icc (-R) R) := by
    obtain ⟨C, h⟩ := semicircle_polynomial_holder (U ℝ ((j.toNat : ℤ) - 1))
    exact subtractedRealCauchy_integrable h (by norm_num) hR z
  have heq (t : ℝ) : t / (t ^ 2 + z.im ^ 2) *
      ((∑ j ∈ s, d j * trialMode j.toNat (z.re + t)) -
        ∑ j ∈ s, d j * trialMode j.toNat z.re) = ∑ j ∈ s, d j * g j t := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by dsimp [g]; ring
  simp only [subtractedRealCauchy, heq, integral_finsetSum _ (fun j _ => (hint j).const_mul (d j)),
    integral_const_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by dsimp [g]; ring

/-- The actual real Cauchy boundary value of the finite profile equals the
polynomial coordinate of the reconstructed curve, including both endpoints. -/
theorem finite_realCauchyBoundary (s : Finset ℤ) (d : ℤ → ℝ) (hs : ∀ j ∈ s, 0 < j)
    {x : ℝ} (hx : |x| ≤ 1) : realCauchyBoundaryRe (traceHeight s d) x = traceReal s d x := by
  have hfun : traceHeight s d = fun t => ∑ j ∈ s, d j * trialMode j.toNat t := by
    funext t
    exact Finset.sum_congr rfl fun j hj => by rw [mode_sine_global j (hs j hj)]
  rw [hfun, realCauchyBoundaryRe, subtracted_modes_sum _ _ _ (by positivity), traceReal, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hpos : 0 < j.toNat := by have := hs j hj; omega
  have h := congrArg Complex.re (trialMode_cauchyExtension j.toNat hpos (ofReal_mem_closure_upperHalfPlane x))
  rw [realCauchyExtension_ofReal, modeExtension_re _ hx, Int.toNat_of_nonneg (hs j hj).le] at h
  have hval : realCauchyBoundaryRe (trialMode j.toNat) x = -(T ℝ j).eval x := by simpa [Complex.mul_re] using h
  rw [← realCauchyBoundaryRe, hval, mul_neg]

/-- Section 7's two finite coordinates are the boundary limit of the actual
complex Cauchy integral. -/
theorem finite_cauchyTrace (s : Finset ℤ) (d : ℤ → ℝ) (hs : ∀ j ∈ s, 0 < j)
    {x : ℝ} (hx : |x| ≤ 1) : realCauchyExtension (traceHeight s d) x =
      (traceReal s d x : ℂ) + (traceHeight s d x : ℂ) * Complex.I := by
  rw [realCauchyExtension_ofReal, finite_realCauchyBoundary s d hs hx]

/-- The complex Cauchy integral converges to the reconstructed point along
every approach from the upper half-plane, including at the endpoints. -/
theorem finite_cauchyTrace_tendsto (s : Finset ℤ) (d : ℤ → ℝ) (hs : ∀ j ∈ s, 0 < j)
    {x : ℝ} (hx : |x| ≤ 1) :
    Tendsto (realCauchy (traceHeight s d)) (𝓝[upperHalfPlane] (x : ℂ))
      (𝓝 ((traceReal s d x : ℂ) + (traceHeight s d x : ℂ) * Complex.I)) := by
  let p := ∑ j ∈ s, Polynomial.C (d j) * U ℝ ((j.toNat : ℤ) - 1)
  have hp : traceHeight s d = fun y => semicircleBarrier y * p.eval y := by
    funext y
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Finset.mul_sum, traceHeight]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mode_sine_global j (hs j hj), trialMode]
    ring
  obtain ⟨C, h⟩ := semicircle_polynomial_holder p
  rw [← hp] at h
  have hz (y : ℝ) (hy : 1 ≤ |y|) : traceHeight s d y = 0 := by
    rw [hp]
    simp [semicircleBarrier_zero_exterior y hy]
  simpa only [finite_realCauchyBoundary s d hs hx] using
    realCauchy_boundary_tendsto h (by norm_num) hz x

/-- The signed Green integral calculated directly from the Cauchy boundary
trace equals the weighted finite sum. -/
theorem cauchyTrace_signedArea (s : Finset ℤ) (d : ℤ → ℝ) (hs : ∀ j ∈ s, 0 < j) :
    -(∫ t in (-1 : ℝ)..1, traceHeight s d t * deriv (realCauchyBoundaryRe (traceHeight s d)) t) =
      Real.pi / 2 * ∑ j ∈ s, (j : ℝ) * (d j)^2 := by
  rw [← physicalTraceArea s d hs]
  congr 1
  simp only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have he : realCauchyBoundaryRe (traceHeight s d) =ᶠ[𝓝 t] traceReal s d := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
    exact finite_realCauchyBoundary _ _ hs (abs_le.mpr ⟨hy.1.le,hy.2.le⟩)
  dsimp only
  rw [he.deriv_eq]

end Torsion.Galerkin

module

public import Torsion.WeakHarmonicWeyl.Classical
public import Torsion.SobolevIsometry
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-! # Distributional Laplacian of a planar half-space ramp

The normal second derivative is the unit line measure on the boundary.
Tangential second derivatives integrate to zero on each complete line. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion.HermiteHadamard
open WeakHarmonicRegularity

private theorem ramp_second_integral {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ x : ℝ, max 0 x * deriv (deriv f) x) = f 0 := by
  let p : ℝ → ℝ := fun x => x * deriv f x - f x
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have hp : ContDiff ℝ ∞ p := (contDiff_id.mul hd).sub hf
  have hpc : HasCompactSupport p := (hc.deriv.mul_left).sub hc
  have hder (x : ℝ) : deriv p x = x * deriv (deriv f) x := by
    have h := (((hasDerivAt_id x).mul ((hd.differentiable (by simp) x).hasDerivAt)).sub
      ((hf.differentiable (by simp) x).hasDerivAt)).deriv
    change deriv (id * deriv f - f) x = _
    simpa [id_eq] using h
  calc
    _ = ∫ x in Ioi 0, deriv p x := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        by_cases hx : 0 < x
        · simp [indicator_of_mem (show x ∈ Ioi 0 from hx), max_eq_right hx.le, hder]
        · simp [indicator_of_notMem (show x ∉ Ioi 0 from hx), max_eq_left (le_of_not_gt hx)]
    _ = f 0 := by
      rw [hpc.integral_Ioi_deriv_eq (hp.of_le (by simp))]
      simp [p]

private theorem second_integral_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : (∫ x : ℝ, deriv (deriv f) x) = 0 := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => (hd.differentiable (by simp) x).hasDerivAt)
    ((hd.continuous_deriv (by simp)).integrable_of_hasCompactSupport hc.deriv.deriv)
    (hd.continuous.integrable_of_hasCompactSupport hc.deriv)

private def axisDeriv (f : Plane → ℝ) (v : Plane) (z : Plane) := fderiv ℝ f z v

private theorem axisDeriv_smooth {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (v : Plane) :
    ContDiff ℝ ∞ (axisDeriv f v) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem ramp_trace (n : Plane) (hn : ‖n‖ = 1) (L : Plane →L[ℝ] Plane) :
    (L 1).re + (L Complex.I).im = inner ℝ (L n) n +
      inner ℝ (L (Complex.I * n)) (Complex.I * n) := by
  have hcoord (v : Plane) : L v = v.re • L (1 : Plane) + v.im • L Complex.I := by
    exact (congrArg L (show v = v.re • (1 : Plane) + v.im • Complex.I by
      apply Complex.ext <;> simp)).trans (by simp only [map_add, map_smul])
  have hs : n.re * n.re + n.im * n.im = 1 := by
    change Complex.normSq n = 1
    rw [← Complex.sq_norm, hn, one_pow]
  rw [hcoord n, hcoord (Complex.I * n)]
  simp [Complex.inner, Complex.mul_re, Complex.mul_im]
  linear_combination -((L 1).re + (L Complex.I).im) * hs

private theorem axisDeriv_second {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b) (v z : Plane) :
    axisDeriv (axisDeriv b v) v z = inner ℝ (fderiv ℝ (gradient b) z v) v := by
  rw [fderiv_gradient_inner hb]
  let A := ContinuousLinearMap.apply ℝ ℝ v
  have h := (A.hasFDerivAt.comp z
    ((hb.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z).hasFDerivAt).fderiv
  have hh := congrArg (fun L : Plane →L[ℝ] ℝ => L v) h
  exact hh

private theorem axisDeriv_line {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (v a : Plane) (t : ℝ) :
    deriv (fun x : ℝ => f (x • v + a)) t = axisDeriv f v (t • v + a) := by
  have h : HasDerivAt (fun x : ℝ => x • v + a) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).add_const a
  exact (((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t h)).deriv

private theorem second_axisDeriv_line {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (v a : Plane) (t : ℝ) :
    deriv (deriv (fun x : ℝ => f (x • v + a))) t =
      axisDeriv (axisDeriv f v) v (t • v + a) := by
  rw [show deriv (fun x : ℝ => f (x • v + a)) =
        (fun x => axisDeriv f v (x • v + a)) from funext (axisDeriv_line hf v a)]
  exact axisDeriv_line (axisDeriv_smooth hf v) v a t

/-- The distributional Laplacian of the one-sided unit-slope ramp is
Euclidean arclength on its boundary line, evaluated against any smooth compact test. -/
theorem halfPlaneRamp_integral_laplacian (n : Plane) (hn : ‖n‖ = 1) {b : Plane → ℝ}
    (hb : IsTest univ b) :
    (∫ z : Plane, max 0 (inner ℝ n z) * planarLaplacian b z) =
      ∫ t : ℝ, b (t • (Complex.I * n)) := by
  let v := Complex.I * n
  let a : Circle := ⟨n, by simpa [Submonoid.unitSphere] using hn⟩
  let e := rotation a
  let R : (ℝ × ℝ) ≃ₜ Plane := Complex.equivRealProdCLM.symm.toHomeomorph.trans e.toHomeomorph
  have hR (p : ℝ × ℝ) : R p = p.1 • n + p.2 • v := by
    change n * (Complex.equivRealProdCLM.symm p) = _
    rw [Complex.equivRealProdCLM_symm_apply]
    simp only [v, Complex.real_smul]
    ring
  have hMP : MeasurePreserving R volume volume :=
    e.measurePreserving.comp Complex.volume_preserving_equiv_real_prod.symm
  have hcross : inner ℝ n v = 0 := by
    simp [v, Complex.inner, Complex.mul_re, Complex.mul_im]
    ring
  have hinner (p : ℝ × ℝ) : inner ℝ n (R p) = p.1 := by
    simp only [hR, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn,
      hcross, one_pow, mul_one, mul_zero, add_zero]
  let d₂ (w z : Plane) := axisDeriv (axisDeriv b w) w z
  have hLap (z : Plane) : planarLaplacian b z = d₂ n z + d₂ v z := by
    simpa only [d₂, v, planarLaplacian, planarDivergence, axisDeriv_second hb.1] using ramp_trace n hn (fderiv ℝ (gradient b) z)
  let T (w : Plane) (p : ℝ × ℝ) := max 0 p.1 * d₂ w (R p)
  have hint (w : Plane) : Integrable (T w) ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact ((continuous_const.max continuous_fst).mul
      ((axisDeriv_smooth (axisDeriv_smooth hb.1 w) w).continuous.comp R.continuous)
      ).integrable_of_hasCompactSupport
        (((hb.2.1.fderiv_apply ℝ w).fderiv_apply ℝ w).comp_homeomorph R).mul_left
  have hbc : HasCompactSupport (b ∘ R) := hb.2.1.comp_homeomorph R
  have hcX (y : ℝ) : HasCompactSupport (fun x : ℝ => b (x • n + y • v)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hbc.image continuous_fst)
    intro x hx
    refine ⟨(x,y), subset_tsupport _ ?_, rfl⟩
    simpa only [Function.mem_support, Function.comp_apply, hR] using hx
  have hcY (x : ℝ) : HasCompactSupport (fun y : ℝ => b (y • v + x • n)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hbc.image continuous_snd)
    intro y hy
    refine ⟨(x,y), subset_tsupport _ ?_, rfl⟩
    simpa only [Function.mem_support, Function.comp_apply, hR, add_comm (x • n) (y • v)] using hy
  have hX (y : ℝ) : (∫ x : ℝ, T n (x,y)) = b (y • v) := by
    have hh := ramp_second_integral (hb.1.comp (show
      ContDiff ℝ ∞ (fun x : ℝ => x • n + y • v) by fun_prop)) (hcX y)
    simpa only [Function.comp_def, second_axisDeriv_line hb.1, zero_smul, zero_add, T, d₂, hR] using hh
  have hY (x : ℝ) : (∫ y : ℝ, T v (x,y)) = 0 := by
    have hh := second_integral_zero (hb.1.comp (show
      ContDiff ℝ ∞ (fun y : ℝ => y • v + x • n) by fun_prop)) (hcY x)
    simp only [Function.comp_def, second_axisDeriv_line hb.1] at hh
    simp only [T, d₂, hR, add_comm (x • n) (_ • v), integral_const_mul, hh, mul_zero]
  calc
    _ = ∫ p : ℝ × ℝ, max 0 (inner ℝ n (R p)) * planarLaplacian b (R p) := by
      exact (hMP.integral_comp R.toMeasurableEquiv.measurableEmbedding
        (fun z => max 0 (inner ℝ n z) * planarLaplacian b z)).symm
    _ = ∫ p, T n p + T v p ∂(volume : Measure ℝ).prod volume := by
      rw [Measure.volume_eq_prod]
      simp only [hinner, hLap, mul_add, T]
    _ = (∫ y : ℝ, ∫ x : ℝ, T n (x,y)) + ∫ x : ℝ, ∫ y : ℝ, T v (x,y) := by
      rw [integral_add (hint n) (hint v), integral_prod_symm _ (hint n), integral_prod _ (hint v)]
    _ = _ := by simp only [hX, hY, integral_zero, add_zero, v]

/-- A radial test has the same line integral for every orientation of the half-plane. -/
theorem halfPlaneRamp_integral_laplacian_radial (n : Plane) (hn : ‖n‖ = 1)
    {b : Plane → ℝ} (hb : IsTest univ b) {β : ℝ → ℝ} (hβ : ∀ z, b z = β ‖z‖) :
    (∫ z : Plane, max 0 (inner ℝ n z) * planarLaplacian b z) =
      ∫ t : ℝ, β |t| := by
  rw [halfPlaneRamp_integral_laplacian n hn hb]
  simp only [hβ, norm_smul, Real.norm_eq_abs, norm_mul, Complex.norm_I, hn, mul_one]

end Torsion.HermiteHadamard

import Torsion.WeakHarmonicRegularity
import Torsion.ComplexIdentity
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Classical calculus of the physical torsion formula

The gradient and Poisson equation for the candidate in Lemma 7.1 are
calculated from holomorphy. These results do not assert zero boundary trace
or H¹₀ membership, which remain separate steps in identifying weak torsion.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace Torsion.PhysicalTorsion

/-- The physical candidate in (7.1). -/
def candidate (B : Plane → Plane) (w : Plane) : ℝ :=
  -(w.im) ^ 2 / 2 + (B w).im

/-- The complex gradient prescribed by the Cauchy--Riemann equations. -/
def candidateGradient (B : Plane → Plane) (w : Plane) : Plane :=
  Complex.I * star (deriv B w) - (w.im : ℂ) * Complex.I

/-- The gradient of the imaginary part of a holomorphic function is the
positively rotated conjugate of its complex derivative. -/
theorem hasGradientAt_im_of_hasDerivAt {B : Plane → Plane} {d w : Plane}
    (hB : HasDerivAt B d w) :
    HasGradientAt (fun z => (B z).im) (Complex.I * star d) w := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert (Complex.imCLM.hasFDerivAt.comp w hB.complexToReal_fderiv) using 1
  ext v
  simp [InnerProductSpace.toDual_apply, ContinuousLinearMap.comp_apply,
    Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

/-- The candidate has the stated actual real gradient at every holomorphy
point. No boundary-gradient formula is assumed. -/
theorem candidate_hasGradientAt {B : Plane → Plane} {w : Plane}
    (hB : DifferentiableAt ℂ B w) :
    HasGradientAt (candidate B) (candidateGradient B w) w := by
  have hi := Complex.imCLM.hasFDerivAt (x := w)
  have hq : HasFDerivAt (fun z : Plane => -(z.im) ^ 2 / 2)
      ((-w.im) • Complex.imCLM) w := by
    convert (hi.mul hi).const_mul (-(1 / 2 : ℝ)) using 1 <;>
      ext v <;> simp <;> ring
  have hb := Complex.imCLM.hasFDerivAt.comp w hB.hasDerivAt.complexToReal_fderiv
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hq.add hb using 1
  ext v
  simp [candidateGradient, InnerProductSpace.toDual_apply,
    ContinuousLinearMap.comp_apply, Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

theorem gradient_candidate {B : Plane → Plane} {w : Plane}
    (hB : DifferentiableAt ℂ B w) :
    gradient (candidate B) w = candidateGradient B w :=
  (candidate_hasGradientAt hB).gradient

/-- The two physical coordinate components in the proof of Lemma 7.1. -/
theorem gradient_candidate_components {B : Plane → Plane} {w : Plane}
    (hB : DifferentiableAt ℂ B w) :
    (gradient (candidate B) w).re = (deriv B w).im ∧
      (gradient (candidate B) w).im = -w.im + (deriv B w).re := by
  rw [gradient_candidate hB]
  simp [candidateGradient, Complex.mul_re, Complex.mul_im, add_comm, sub_eq_add_neg]

/-- The divergence of the actual candidate gradient is -1 whenever the
complex derivative is itself differentiable. -/
theorem divergence_candidateGradient {B : Plane → Plane} {w : Plane}
    (hD : DifferentiableAt ℂ (deriv B) w) :
    WeakHarmonicRegularity.planarDivergence (candidateGradient B) w = -1 := by
  have h1 := ((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp w
    hD.hasDerivAt.complexToReal_fderiv).const_mul Complex.I
  have h2 := ((Complex.ofRealCLM.hasFDerivAt).comp w
    (Complex.imCLM.hasFDerivAt (x := w))).mul_const Complex.I
  have h := h1.sub h2
  change HasFDerivAt (candidateGradient B) _ w at h
  unfold WeakHarmonicRegularity.planarDivergence
  change (fderiv ℝ (candidateGradient B) w 1).re +
    (fderiv ℝ (candidateGradient B) w Complex.I).im = -1
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The candidate solves the actual classical Poisson equation on every
open region where the physical holomorphic function and its derivative are
differentiable. Boundary admissibility is not hidden in this statement. -/
theorem candidate_laplacian_eq_neg_one {U : Set Plane} (hU : IsOpen U)
    {B : Plane → Plane} (hB : DifferentiableOn ℂ B U)
    (hD : DifferentiableOn ℂ (deriv B) U) {w : Plane} (hw : w ∈ U) :
    WeakHarmonicRegularity.planarLaplacian (candidate B) w = -1 := by
  have heq : gradient (candidate B) =ᶠ[𝓝 w] candidateGradient B := by
    filter_upwards [hU.mem_nhds hw] with z hz
    exact gradient_candidate (hB.differentiableAt (hU.mem_nhds hz))
  unfold WeakHarmonicRegularity.planarLaplacian WeakHarmonicRegularity.planarDivergence
  rw [heq.fderiv_eq]
  exact divergence_candidateGradient (hD.differentiableAt (hU.mem_nhds hw))

end Torsion.PhysicalTorsion

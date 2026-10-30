import Torsion.ComplexPrimitives
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Holomorphic continuation through a first-order linear equation

A solution on an upper half-disc extends to the whole disc when its
inhomogeneous term does. The proof constructs the extension with the
ordinary exponential integrating factor and a genuine holomorphic primitive.
-/
noncomputable section
open Complex Set
open scoped Topology

namespace Torsion.ComplexReflection

/-- A holomorphic solution of `P' = c P + H` on an upper half-disc extends
holomorphically to the whole disc if the actual inhomogeneous term `H`
is holomorphic there. -/
theorem exists_ode_extension_upper_ball {P H : ℂ → ℂ} {x r : ℝ} {c : ℂ}
    (hr : 0 < r) (hH : DifferentiableOn ℂ H (Metric.ball (x : ℂ) r))
    (hODE : ∀ z ∈ Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im},
      HasDerivAt P (c * P z + H z) z) :
    ∃ Q : ℂ → ℂ, DifferentiableOn ℂ Q (Metric.ball (x : ℂ) r) ∧
      EqOn Q P (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
      ∀ z ∈ Metric.ball (x : ℂ) r, HasDerivAt Q (c * Q z + H z) z := by
  let U := Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}
  let e : ℂ → ℂ := fun z => Complex.exp (-c * z)
  have he (z : ℂ) : HasDerivAt e (e z * -c) z :=
    by simpa only [e, id_eq, mul_one] using ((hasDerivAt_id z).const_mul (-c)).cexp
  have heD : DifferentiableOn ℂ e (Metric.ball (x : ℂ) r) :=
    fun z _ => (he z).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun z => e z * H z) (Metric.ball (x : ℂ) r) := heD.mul hH
  obtain ⟨K, hK⟩ := hg.isExactOn_ball
  let z₀ : ℂ := (x : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I
  have hz₀ : z₀ ∈ U := by
    constructor
    · have hd : dist z₀ (x : ℂ) = r / 2 := by
        simp [z₀, dist_eq_norm, abs_of_pos hr]
      rw [Metric.mem_ball, hd]
      linarith
    · simpa [z₀] using half_pos hr
  let L : ℂ → ℂ := fun z => K z - K z₀ + e z₀ * P z₀
  have hL (z : ℂ) (hz : z ∈ Metric.ball (x : ℂ) r) :
      HasDerivAt L (e z * H z) z :=
    ((hK z hz).sub_const (K z₀)).add_const (e z₀ * P z₀)
  have hUopen : IsOpen U := Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hUconn : IsPreconnected U :=
    ((convex_ball (x : ℂ) r).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hprod (z : ℂ) (hz : z ∈ U) :
      HasDerivAt (fun w => e w * P w) (e z * H z) z := by
    convert (he z).mul (hODE z hz) using 1; dsimp only [e]; ring
  have heq : EqOn (fun z => e z * P z) L U := by
    apply hUopen.eqOn_of_deriv_eq hUconn
      (fun z hz => (hprod z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hL z hz.1).differentiableAt.differentiableWithinAt)
    · intro z hz
      exact (hprod z hz).deriv.trans (hL z hz.1).deriv.symm
    · exact hz₀
    · simp [L]
  let Q : ℂ → ℂ := fun z => Complex.exp (c * z) * L z
  have hQ (z : ℂ) (hz : z ∈ Metric.ball (x : ℂ) r) :
      HasDerivAt Q (c * Q z + H z) z := by
    have hexp : Complex.exp (c * z) * e z = 1 := by
      dsimp only [e]
      rw [← Complex.exp_add, show c * z + -c * z = 0 by ring, Complex.exp_zero]
    have hd := (((hasDerivAt_id z).const_mul c).cexp).mul (hL z hz)
    simp only [id_eq, mul_one] at hd
    convert hd using 1
    dsimp only [Q]
    rw [show Complex.exp (c * z) * (e z * H z) =
      (Complex.exp (c * z) * e z) * H z by ring, hexp]
    ring
  refine ⟨Q, fun z hz => (hQ z hz).differentiableAt.differentiableWithinAt, ?_, hQ⟩
  intro z hz
  change Complex.exp (c * z) * L z = P z
  rw [← heq hz, ← mul_assoc]
  have hexp : Complex.exp (c * z) * e z = 1 := by
    dsimp only [e]
    rw [← Complex.exp_add, show c * z + -c * z = 0 by ring, Complex.exp_zero]
  rw [hexp, one_mul]

/-- The same extension agrees with the original function on the closed
upper half-disc whenever that function is continuous up to its diameter. -/
theorem exists_ode_extension_closed_upper_ball {P H : ℂ → ℂ} {x r : ℝ} {c : ℂ}
    (hr : 0 < r) (hH : DifferentiableOn ℂ H (Metric.ball (x : ℂ) r))
    (hP : ContinuousOn P (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}))
    (hODE : ∀ z ∈ Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im},
      HasDerivAt P (c * P z + H z) z) :
    ∃ Q : ℂ → ℂ, DifferentiableOn ℂ Q (Metric.ball (x : ℂ) r) ∧
      EqOn Q P (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      ∀ z ∈ Metric.ball (x : ℂ) r, HasDerivAt Q (c * Q z + H z) z := by
  obtain ⟨Q, hQ, heq, hQODE⟩ := exists_ode_extension_upper_ball hr hH hODE
  refine ⟨Q, hQ, ?_, hQODE⟩
  apply heq.of_subset_closure (hQ.continuousOn.mono inter_subset_left) hP
  · exact fun z hz => ⟨hz.1, (show 0 < z.im from hz.2).le⟩
  · have hcl : closure {z : ℂ | 0 < z.im} = {z : ℂ | 0 ≤ z.im} :=
      Complex.closure_setOf_lt_im 0
    rw [← hcl]
    exact Metric.isOpen_ball.inter_closure

end Torsion.ComplexReflection

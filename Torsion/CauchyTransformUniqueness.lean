import Torsion.SpectralDefinitions
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Convex

/-!
# Bounded holomorphic uniqueness in the upper half-plane

A bounded holomorphic function, continuous on the closed half-plane and
real on its boundary, is constant. The proof applies Phragmen--Lindelof to
`exp(±i h)` and then the maximum modulus principle to `(h-i)/(h+i)`.
Convergence to zero along any interior path identifies the constant as zero.
-/

noncomputable section
open Set Filter Complex Asymptotics Bornology
open scoped Topology

namespace Torsion.Spectral

private theorem rotate_right_to_upper (w : ℂ) (hw : 0 < w.re) :
    Complex.I * w ∈ upperHalfPlane := by
  simpa [upperHalfPlane, Complex.mul_im] using hw

private theorem I_mul_neg_I_mul (z : ℂ) : Complex.I * (-Complex.I * z) = z := by
  rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]

private theorem I_mul_real_I (x : ℝ) : Complex.I * ((x : ℂ) * Complex.I) = (-x : ℝ) := by
  calc
    Complex.I * ((x : ℂ) * Complex.I) = (x : ℂ) * (Complex.I * Complex.I) := by ring
    _ = (-x : ℝ) := by simp

/-- The first maximum-principle step: boundedness and real boundary data
give `‖exp(i h)‖ ≤ 1` throughout H. -/
theorem norm_exp_I_mul_le_one_of_real_boundary {h : ℂ → ℂ}
    (hd : DiffContOnCl ℂ h upperHalfPlane) (B : ℝ)
    (hb : ∀ z ∈ upperHalfPlane, ‖h z‖ ≤ B)
    (hr : ∀ x : ℝ, (h (x : ℂ)).im = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    ‖Complex.exp (Complex.I * h z)‖ ≤ 1 := by
  let f : ℂ → ℂ := fun w => Complex.exp (Complex.I * h (Complex.I * w))
  have hrot : DiffContOnCl ℂ (fun w : ℂ => h (Complex.I * w)) {w : ℂ | 0 < w.re} :=
    hd.comp (differentiable_id.const_mul Complex.I).diffContOnCl
      (fun w hw => rotate_right_to_upper w hw)
  have hfd : DiffContOnCl ℂ f {w : ℂ | 0 < w.re} := by
    constructor
    · exact ((differentiableOn_const Complex.I).mul hrot.differentiableOn).cexp
    · exact Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hrot.continuousOn)
  have hfbound : ∀ w : ℂ, 0 < w.re → ‖f w‖ ≤ Real.exp B := by
    intro w hw
    have hi : -(h (Complex.I * w)).im ≤ ‖h (Complex.I * w)‖ :=
      (neg_le_abs _).trans (Complex.abs_im_le_norm _)
    dsimp [f]
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.2
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
    exact hi.trans (hb _ (rotate_right_to_upper w hw))
  have hgrowth : ∃ c < (2 : ℝ), ∃ D,
      f =O[cobounded ℂ ⊓ 𝓟 {w : ℂ | 0 < w.re}]
        (fun w => Real.exp (D * ‖w‖ ^ c)) := by
    refine ⟨0, by norm_num, 0, Asymptotics.IsBigO.of_bound (Real.exp B) ?_⟩
    apply eventually_inf_principal.2
    exact Eventually.of_forall fun w hw => by simpa using hfbound w hw
  have hrealbound : IsBoundedUnder (· ≤ ·) atTop (fun x : ℝ => ‖f (x : ℂ)‖) := by
    apply isBoundedUnder_of_eventually_le (a := Real.exp B)
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact hfbound (x : ℂ) (by simpa using hx)
  have hboundary : ∀ x : ℝ, ‖f ((x : ℂ) * Complex.I)‖ ≤ 1 := by
    intro x
    dsimp [f]
    rw [I_mul_real_I, Complex.norm_exp]
    have hh : (h (-(x : ℂ))).im = 0 := by simpa using hr (-x)
    simp [Complex.mul_re, hh]
  have hw : 0 ≤ (-Complex.I * z).re := by
    simpa [Complex.mul_re] using (show 0 ≤ z.im from hz.le)
  have h := PhragmenLindelof.right_half_plane_of_bounded_on_real
    hfd hgrowth hrealbound hboundary hw
  simpa only [f, I_mul_neg_I_mul] using h

/-- A bounded holomorphic function with real boundary data is real valued
throughout the upper half-plane. -/
theorem im_eq_zero_of_bounded_holomorphic_real_boundary {h : ℂ → ℂ}
    (hd : DiffContOnCl ℂ h upperHalfPlane) (B : ℝ)
    (hb : ∀ z ∈ upperHalfPlane, ‖h z‖ ≤ B)
    (hr : ∀ x : ℝ, (h (x : ℂ)).im = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (h z).im = 0 := by
  have hplus := norm_exp_I_mul_le_one_of_real_boundary hd B hb hr hz
  have hdneg : DiffContOnCl ℂ (fun w => -h w) upperHalfPlane :=
    ⟨hd.differentiableOn.neg, hd.continuousOn.neg⟩
  have hminus := norm_exp_I_mul_le_one_of_real_boundary hdneg B
    (fun w hw => by simpa using hb w hw) (fun x => by simp [hr x]) hz
  rw [Complex.norm_exp, Real.exp_le_one_iff] at hplus hminus
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, Complex.neg_im, neg_neg] at hplus hminus
  linarith

/-- Bounded holomorphic real-boundary uniqueness: the function is constant.
This is the analytic uniqueness step used in Lemma 5.2. -/
theorem bounded_holomorphic_real_boundary_constant {h : ℂ → ℂ}
    (hd : DiffContOnCl ℂ h upperHalfPlane) (B : ℝ)
    (hb : ∀ z ∈ upperHalfPlane, ‖h z‖ ≤ B)
    (hr : ∀ x : ℝ, (h (x : ℂ)).im = 0) :
    ∀ z ∈ upperHalfPlane, h z = h Complex.I := by
  have him : ∀ z ∈ upperHalfPlane, (h z).im = 0 :=
    fun _ hz => im_eq_zero_of_bounded_holomorphic_real_boundary hd B hb hr hz
  have hden : ∀ z ∈ upperHalfPlane, h z + Complex.I ≠ 0 := by
    intro z hz heq
    have hi := congrArg Complex.im heq
    simp [him z hz] at hi
  let g : ℂ → ℂ := fun z => (h z - Complex.I) / (h z + Complex.I)
  have hgd : DifferentiableOn ℂ g upperHalfPlane :=
    (hd.differentiableOn.sub_const Complex.I).div
      (hd.differentiableOn.add_const Complex.I) hden
  have hnorm : ∀ z ∈ upperHalfPlane, ‖g z‖ = 1 := by
    intro z hz
    have hn : ‖h z - Complex.I‖ = ‖h z + Complex.I‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply, him z hz]
    dsimp [g]
    rw [norm_div, hn, div_self (norm_ne_zero_iff.2 (hden z hz))]
  have hI : Complex.I ∈ upperHalfPlane := by simp [upperHalfPlane]
  have hmax : IsMaxOn (norm ∘ g) upperHalfPlane Complex.I := by
    intro z hz
    change ‖g z‖ ≤ ‖g Complex.I‖
    rw [hnorm z hz, hnorm Complex.I hI]
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
    (isOpen_lt continuous_const Complex.continuous_im) hgd hI hmax
  intro z hz
  have heq : g z = g Complex.I := hconst hz
  change (h z - Complex.I) / (h z + Complex.I) =
    (h Complex.I - Complex.I) / (h Complex.I + Complex.I) at heq
  have heq' := (div_eq_div_iff (hden z hz) (hden Complex.I hI)).1 heq
  have hmul : (2 * Complex.I) * (h z - h Complex.I) = 0 := by linear_combination heq'
  exact sub_eq_zero.1 ((mul_eq_zero.1 hmul).resolve_left
    (mul_ne_zero (by norm_num) Complex.I_ne_zero))

/-- A single interior decay path suffices to identify the preceding
constant as zero. No compactification or reflection principle is assumed. -/
theorem bounded_holomorphic_real_boundary_eq_zero {h : ℂ → ℂ}
    (hd : DiffContOnCl ℂ h upperHalfPlane) (B : ℝ)
    (hb : ∀ z ∈ upperHalfPlane, ‖h z‖ ≤ B)
    (hr : ∀ x : ℝ, (h (x : ℂ)).im = 0)
    {zseq : ℕ → ℂ} (hseq : ∀ᶠ n in atTop, zseq n ∈ upperHalfPlane)
    (hzero : Tendsto (fun n => h (zseq n)) atTop (𝓝 0)) :
    ∀ z ∈ upperHalfPlane, h z = 0 := by
  have hconst := bounded_holomorphic_real_boundary_constant hd B hb hr
  have hlim : Tendsto (fun _ : ℕ => h Complex.I) atTop (𝓝 0) := by
    apply hzero.congr'
    filter_upwards [hseq] with n hn
    exact hconst _ hn
  have hI : h Complex.I = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  intro z hz
  exact (hconst z hz).trans hI

end Torsion.Spectral

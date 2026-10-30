module

public import Torsion.RestrictedSpectralLatticeApprox

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Odd folding and flat smooth approximations on the positive half interval

The sign is attached to the spatial coordinate. Scalar smoothing is first
made identically zero near the value zero, so odd folding of a smooth odd
core function remains genuinely smooth at the origin.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- Extend the scalar-transformed positive half of a density oddly. -/
def oddFoldComp (Φ f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then Φ (f x) else -Φ (f x)

/-- Absolute value on the positive half, extended oddly to the line. -/
def oddFoldAbs (f : ℝ → ℝ) : ℝ → ℝ := oddFoldComp abs f

@[simp] theorem oddFoldAbs_of_nonneg {f : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x) :
    oddFoldAbs f x = |f x| := by simp [oddFoldAbs, oddFoldComp, hx]

@[simp] theorem oddFoldAbs_of_neg {f : ℝ → ℝ} {x : ℝ} (hx : x < 0) :
    oddFoldAbs f x = -|f x| := by simp [oddFoldAbs, oddFoldComp, not_le.mpr hx]

@[simp] theorem oddFoldAbs_norm (f : ℝ → ℝ) (x : ℝ) : ‖oddFoldAbs f x‖ = ‖f x‖ := by
  by_cases hx : 0 ≤ x <;> simp [oddFoldAbs, oddFoldComp, hx, Real.norm_eq_abs]

@[simp] theorem oddFoldAbs_sq (f : ℝ → ℝ) (x : ℝ) : (oddFoldAbs f x) ^ 2 = (f x) ^ 2 := by
  by_cases hx : 0 ≤ x <;> simp [oddFoldAbs, oddFoldComp, hx]

theorem oddFoldComp_odd {Φ f : ℝ → ℝ} (hf : Function.Odd f) (hΦ : Function.Even Φ)
    (hΦ0 : Φ 0 = 0) : Function.Odd (oddFoldComp Φ f) := by
  intro x
  have hf0 : f 0 = 0 := by have h := hf 0; simp only [neg_zero] at h; linarith
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [oddFoldComp, not_le.mpr hx, (neg_pos.mpr hx).le, hf x, hΦ (f x)]
  · subst x; simp [oddFoldComp, hf0, hΦ0]
  · simp [oddFoldComp, hx.le, not_le.mpr (neg_neg_of_pos hx), hf x, hΦ (f x)]

theorem oddFoldAbs_odd {f : ℝ → ℝ} (hf : Function.Odd f) : Function.Odd (oddFoldAbs f) :=
  oddFoldComp_odd hf (fun _ => abs_neg _) (by simp)

theorem oddFoldComp_measurable {Φ f : ℝ → ℝ} (hΦ : Measurable Φ) (hf : Measurable f) :
    Measurable (oddFoldComp Φ f) := by
  exact Measurable.ite measurableSet_Ici (hΦ.comp hf) (hΦ.comp hf).neg

/-- A continuous scalar transformation preserves almost-everywhere strong
measurability after attaching the measurable spatial sign. -/
theorem oddFoldComp_aestronglyMeasurable {Φ f : ℝ → ℝ}
    (hΦ : Continuous Φ) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (oddFoldComp Φ f) volume := by
  have hm := hΦ.comp_aestronglyMeasurable hf
  apply (AEStronglyMeasurable.piecewise (s := Ici (0 : ℝ)) measurableSet_Ici hm.restrict hm.neg.restrict).congr
  exact ae_of_all _ fun x => by
    by_cases hx : 0 ≤ x <;> simp [oddFoldComp, Set.piecewise, hx]

theorem oddFoldAbs_memLp {f : ℝ → ℝ} (hf : MemLp f 2 volume) : MemLp (oddFoldAbs f) 2 volume := by
  have hm : AEStronglyMeasurable (oddFoldAbs f) volume :=
    oddFoldComp_aestronglyMeasurable continuous_abs hf.aestronglyMeasurable
  exact hf.of_le hm (ae_of_all _ fun x => (oddFoldAbs_norm f x).le)

/-- A positive shrinking value cutoff. -/
def oddFoldEpsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem oddFoldEpsilon_pos (n : ℕ) : 0 < oddFoldEpsilon n := by unfold oddFoldEpsilon; positivity

theorem tendsto_oddFoldEpsilon : Tendsto oddFoldEpsilon atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- A smooth even absolute-value approximation that is identically zero
on the entire value interval [-εn,εn]. -/
def oddFoldAbsApprox (n : ℕ) (t : ℝ) : ℝ :=
  SmoothPositivePart.approx n (t - oddFoldEpsilon n) +
    SmoothPositivePart.approx n (-t - oddFoldEpsilon n)

theorem oddFoldAbsApprox_even (n : ℕ) : Function.Even (oddFoldAbsApprox n) := by
  intro t
  simp only [oddFoldAbsApprox, neg_neg, add_comm]

theorem oddFoldAbsApprox_zero_on (n : ℕ) {t : ℝ} (ht : |t| ≤ oddFoldEpsilon n) :
    oddFoldAbsApprox n t = 0 := by
  have h := abs_le.1 ht
  rw [oddFoldAbsApprox, SmoothPositivePart.approx_zero_of_nonpos n (by linarith),
    SmoothPositivePart.approx_zero_of_nonpos n (by linarith), add_zero]

@[simp] theorem oddFoldAbsApprox_zero (n : ℕ) : oddFoldAbsApprox n 0 = 0 :=
  oddFoldAbsApprox_zero_on n (by simpa using (oddFoldEpsilon_pos n).le)

theorem oddFoldAbsApprox_contDiff (n : ℕ) : ContDiff ℝ ∞ (oddFoldAbsApprox n) :=
  ((SmoothPositivePart.approx_contDiff n).comp (contDiff_id.sub contDiff_const)).add
    ((SmoothPositivePart.approx_contDiff n).comp (contDiff_neg.sub contDiff_const))

theorem oddFoldAbsApprox_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (oddFoldAbsApprox n)
      (SmoothPositivePart.slope n (t - oddFoldEpsilon n) -
        SmoothPositivePart.slope n (-t - oddFoldEpsilon n)) t := by
  have h1 : HasDerivAt (fun x : ℝ => SmoothPositivePart.approx n (x - oddFoldEpsilon n))
      (SmoothPositivePart.slope n (t - oddFoldEpsilon n)) t := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (SmoothPositivePart.approx_hasDerivAt n (t - oddFoldEpsilon n)).comp t
        ((hasDerivAt_id t).sub_const (oddFoldEpsilon n))
  have h2 : HasDerivAt (fun x : ℝ => SmoothPositivePart.approx n (-x - oddFoldEpsilon n))
      (-SmoothPositivePart.slope n (-t - oddFoldEpsilon n)) t := by
    simpa only [Function.comp_def, mul_neg_one] using
      (SmoothPositivePart.approx_hasDerivAt n (-t - oddFoldEpsilon n)).comp t
        ((hasDerivAt_neg t).sub_const (oddFoldEpsilon n))
  convert h1.add h2 using 1
  all_goals first | rfl | (funext x; rfl) | ring

theorem oddFoldAbsApprox_lipschitz (n : ℕ) : LipschitzWith 1 (oddFoldAbsApprox n) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (oddFoldAbsApprox_hasDerivAt n t).differentiableAt)
  intro t
  rw [(oddFoldAbsApprox_hasDerivAt n t).deriv]
  have hnorm : ‖SmoothPositivePart.slope n (t - oddFoldEpsilon n) -
      SmoothPositivePart.slope n (-t - oddFoldEpsilon n)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [SmoothPositivePart.slope_nonneg n (t - oddFoldEpsilon n),
      SmoothPositivePart.slope_nonneg n (-t - oddFoldEpsilon n),
      SmoothPositivePart.slope_le_one n (t - oddFoldEpsilon n),
      SmoothPositivePart.slope_le_one n (-t - oddFoldEpsilon n)]
  exact_mod_cast hnorm

theorem oddFoldAbsApprox_norm_le (n : ℕ) (t : ℝ) : ‖oddFoldAbsApprox n t‖ ≤ ‖t‖ := by
  simpa only [dist_eq_norm, oddFoldAbsApprox_zero, sub_zero, NNReal.coe_one, one_mul] using
    (oddFoldAbsApprox_lipschitz n).dist_le_mul t 0

private theorem tendsto_shifted_approx (t : ℝ) :
    Tendsto (fun n => SmoothPositivePart.approx n (t - oddFoldEpsilon n)) atTop (𝓝 (max t 0)) := by
  have herr : Tendsto (fun n => SmoothPositivePart.approx n (t - oddFoldEpsilon n) -
      SmoothPositivePart.approx n t) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) tendsto_oddFoldEpsilon
    have h := (SmoothPositivePart.approx_lipschitz n).norm_sub_le (t - oddFoldEpsilon n) t
    simpa only [NNReal.coe_one, one_mul, sub_sub_cancel_left, norm_neg, Real.norm_eq_abs,
      abs_of_pos (oddFoldEpsilon_pos n)] using h
  simpa only [sub_add_cancel, zero_add] using herr.add (SmoothPositivePart.tendsto_approx t)

theorem tendsto_oddFoldAbsApprox (t : ℝ) :
    Tendsto (fun n => oddFoldAbsApprox n t) atTop (𝓝 |t|) := by
  have h := (tendsto_shifted_approx t).add (tendsto_shifted_approx (-t))
  have heq : max t 0 + max (-t) 0 = |t| := by
    rcases le_total 0 t with ht | ht
    · simp [max_eq_left ht, max_eq_right (neg_nonpos.2 ht), abs_of_nonneg ht]
    · simp [max_eq_right ht, max_eq_left (neg_nonneg.2 ht), abs_of_nonpos ht]
  simpa only [oddFoldAbsApprox, heq] using h

end Torsion.Spectral

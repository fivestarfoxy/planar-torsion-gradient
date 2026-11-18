module

public import Torsion.Proof.PaperCurveIsoperimetric
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! # Arclength parametrization and the sharp planar isoperimetric inequality

Extending the positive speed from the parameter interval to a uniformly
positive continuous function gives a global change of variable. Its inverse
parametrizes the original curve by arclength throughout the relevant interval. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Torsion

private theorem exists_speed_orderIso {a b : ℝ} (hab : a < b) {v : ℝ → ℝ}
    (hc : Continuous v) (hv : ∀ t ∈ Icc a b, 0 < v t) :
    ∃ (S : ℝ ≃o ℝ) (M : ℝ → ℝ), Continuous M ∧ (∀ t, 0 < M t) ∧ EqOn M v (Icc a b) ∧
      S a = 0 ∧ S b = (∫ t in a..b, v t) ∧ ∀ t, HasDerivAt (S : ℝ → ℝ) (M t) t := by
  obtain ⟨c, hcI, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hc.continuousOn
  let m := v c
  have hm : 0 < m := hv c hcI
  let M (t : ℝ) := max m (v t)
  have hM : Continuous M := continuous_const.max hc
  have hpos (t : ℝ) : 0 < M t := hm.trans_le (le_max_left _ _)
  have heq : EqOn M v (Icc a b) := fun t ht => max_eq_right (hmin ht)
  let s (t : ℝ) := ∫ x in a..t, M x
  have hd (t : ℝ) : HasDerivAt s (M t) t := (hM.integral_hasStrictDerivAt a t).hasDerivAt
  have ha : s a = 0 := intervalIntegral.integral_same
  have hs := strictMono_of_deriv_pos (f := s) (fun t => (hd t).deriv ▸ hpos t)
  have hdiff : Differentiable ℝ s := fun t => (hd t).differentiableAt
  have hslope {x y : ℝ} (hxy : x ≤ y) : m * (y-x) ≤ s y - s x :=
    mul_sub_le_image_sub_of_le_deriv hdiff (fun t => (hd t).deriv ▸ le_max_left _ _) hxy
  have hsur : Function.Surjective s := by
    apply hdiff.continuous.surjective
    · apply hs.monotone.tendsto_atTop_atTop
      intro y
      let d := |y| / m
      have hd0 : 0 ≤ d := div_nonneg (abs_nonneg _) hm.le
      have hmd : m * d = |y| := by dsimp [d]; field_simp
      refine ⟨a+d, ?_⟩
      have h := hslope (show a ≤ a+d by linarith)
      rw [ha, add_sub_cancel_left, sub_zero, hmd] at h
      exact (le_abs_self _).trans h
    · apply hs.monotone.tendsto_atBot_atBot
      intro y
      let d := |y| / m
      have hd0 : 0 ≤ d := div_nonneg (abs_nonneg _) hm.le
      have hmd : m * d = |y| := by dsimp [d]; field_simp
      refine ⟨a-d, ?_⟩
      have h := hslope (show a-d ≤ a by linarith)
      rw [ha, sub_sub_cancel, zero_sub, hmd] at h
      linarith [neg_abs_le y]
  refine ⟨hs.orderIsoOfSurjective s hsur, M, hM, hpos, heq, ha, ?_, hd⟩
  apply intervalIntegral.integral_congr
  simpa only [uIcc_of_le hab.le] using heq

/-- A regular closed C¹ curve has a globally defined C¹ reparametrization,
unit speed on the arclength interval, preserving the signed cross integral. -/
theorem exists_unitSpeed_closed_reparam {a b : ℝ} (hab : a < b) (γ : ℝ → Plane)
    (hγ : ContDiff ℝ 1 γ) (hv : ∀ t ∈ Icc a b, 0 < ‖deriv γ t‖) (he : γ a = γ b) :
    let L := ∫ t in a..b, ‖deriv γ t‖
    0 < L ∧ ∃ u : ℝ → Plane, ContDiff ℝ 1 u ∧ u 0 = u L ∧
      (∀ t ∈ Icc 0 L, ‖deriv u t‖ = 1) ∧
      (∫ t in a..b, planarCross (γ t) (deriv γ t)) =
        ∫ t in 0..L, planarCross (u t) (deriv u t) := by
  dsimp only
  have hspeed := (hγ.continuous_deriv le_rfl).norm
  obtain ⟨S, M, hM, hpos, hEq, ha, hb, hd⟩ := exists_speed_orderIso hab hspeed hv
  let u : ℝ → Plane := γ ∘ S.symm
  have hSi (t : ℝ) : HasDerivAt (S.symm : ℝ → ℝ) (M (S.symm t))⁻¹ t :=
    (hd _).of_local_left_inverse S.symm.continuous.continuousAt (hpos _).ne'
      (Eventually.of_forall S.apply_symm_apply)
  have hCs : ContDiff ℝ 1 (S : ℝ → ℝ) := contDiff_one_iff_deriv.mpr
    ⟨fun t => (hd t).differentiableAt, (show deriv (S : ℝ → ℝ) = M from funext fun t => (hd t).deriv) ▸ hM⟩
  have hCu : ContDiff ℝ 1 u :=
    hγ.comp (S.toHomeomorph.contDiff_symm_deriv (fun t => (hpos t).ne') hd hCs)
  have du (t : ℝ) : deriv u t = (M (S.symm t))⁻¹ • deriv γ (S.symm t) :=
    (((hγ.differentiable one_ne_zero _).hasDerivAt).scomp t (hSi t)).deriv
  have hL : 0 < S b := ha ▸ S.strictMono hab
  rw [← hb]
  refine ⟨hL, u, hCu, ?_, ?_, ?_⟩
  · simpa only [u, Function.comp_apply, ← ha, S.symm_apply_apply] using he
  · intro t ht
    have hmem : S.symm t ∈ Icc a b :=
      ⟨S.le_symm_apply.mpr (ha ▸ ht.1), S.symm_apply_le.mpr ht.2⟩
    have hm : M (S.symm t) = ‖deriv γ (S.symm t)‖ := hEq hmem
    rw [du, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos _)),
      ← hm, inv_mul_cancel₀ (hpos _).ne']
  · let g (t : ℝ) := planarCross (u t) (deriv u t)
    have hgc : Continuous g := continuous_planarCross hCu.continuous (hCu.continuous_deriv le_rfl)
    have hsub := intervalIntegral.integral_comp_mul_deriv (a := a) (b := b)
      (fun x _ => hd x) hM.continuousOn hgc
    rw [ha] at hsub
    refine Eq.trans (intervalIntegral.integral_congr (g := fun t => (g ∘ S) t * M t) ?_) hsub
    intro t _
    simp only [g, Function.comp_apply, du, u, S.symm_apply_apply, planarCross,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    field_simp [(hpos t).ne']

/-- The sharp signed-area inequality for any regular closed C¹ planar curve. -/
theorem closedCurve_cross_le_length_sq_div_two_pi {a b : ℝ} (hab : a < b) (γ : ℝ → Plane)
    (hγ : ContDiff ℝ 1 γ) (hv : ∀ t ∈ Icc a b, 0 < ‖deriv γ t‖) (he : γ a = γ b) :
    (∫ t in a..b, planarCross (γ t) (deriv γ t)) ≤
      (∫ t in a..b, ‖deriv γ t‖)^2 / (2 * Real.pi) := by
  let L := ∫ t in a..b, ‖deriv γ t‖
  obtain ⟨hL, u, hu, hclosed, hunit, harea⟩ := exists_unitSpeed_closed_reparam hab γ hγ hv he
  change 0 < L at hL
  have h := closedCurve_cross_le_energy hL hu.continuous.continuousOn
    (hu.continuous_deriv le_rfl).continuousOn (fun t _ => (hu.differentiable one_ne_zero t).hasDerivAt) hclosed
  have henergy : (∫ t in 0..L, ‖deriv u t‖^2) = L := by
    calc
      _ = ∫ _t in 0..L, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        change ‖deriv u t‖ ^ 2 = 1
        rw [hunit t (by simpa only [uIcc_of_le hL.le] using ht), one_pow]
      _ = L := by simp
  rw [harea]
  change _ ≤ L^2 / _
  change _ ≤ (L - 0) / _ * (∫ t in 0..L, ‖deriv u t‖^2) at h
  rw [henergy, sub_zero] at h
  exact h.trans_eq (by ring)

end Torsion

module

public import Torsion.ShapeCoefficients
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The planar divergence formula in radial parameters

The radial and angular fundamental theorems of calculus give the flux across
a closed frame. Only the first derivatives of the field and frame occur.
-/

noncomputable section
open Set MeasureTheory
namespace Torsion

/-- Oriented area form in the complex plane, with the real axis first. -/
def planarCross (u v : Plane) : ℝ := u.re * v.im - u.im * v.re

@[fun_prop] theorem continuous_planarCross {X : Type*} [TopologicalSpace X] {u v : X → Plane}
    (hu : Continuous u) (hv : Continuous v) : Continuous (fun x => planarCross (u x) (v x)) := by
  unfold planarCross
  fun_prop

private theorem planarCross_deriv {f g : ℝ → Plane} {f' g' : Plane} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => planarCross (f s) (g s))
      (planarCross f' (g t) + planarCross (f t) g') t := by
  have h₁ := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf).mul
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hg)
  have h₂ := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf).mul
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hg)
  convert h₁.sub h₂ using 1
  · rfl
  · dsimp [planarCross, Function.comp_def]
    ring

private theorem planarCross_trace (L : Plane →L[ℝ] Plane) (u v : Plane) :
    planarCross (L u) v - planarCross (L v) u =
      planarCross u v * ((L 1).re + (L Complex.I).im) := by
  have hL (x : Plane) : L x = x.re • L 1 + x.im • L Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add]
    apply congrArg L
    simp [Complex.real_smul]
  rw [hL u, hL v]
  simp [planarCross, Complex.real_smul, Complex.mul_re, Complex.mul_im]
  ring

/-- On a radially parametrized closed frame the integrated divergence equals
the signed outer boundary flux. The parametrization may have any center or
winding; the Jacobian carries its orientation. -/
theorem radialFrame_divergence (c : Plane) (γ : ℝ → Plane) (W : Plane → Plane)
    (a b : ℝ) (hγ : ContDiff ℝ 1 γ) (hW : ContDiff ℝ 1 W) (hclosed : γ a = γ b) :
    (∫ θ in a..b, ∫ r in (0:ℝ)..1,
      r * planarCross (γ θ-c) (deriv γ θ) * Shape.divergence W (c + r • (γ θ-c))) =
      ∫ θ in a..b, planarCross (W (γ θ)) (deriv γ θ) := by
  let u (θ : ℝ) := γ θ-c
  let v := deriv γ
  let F (θ r : ℝ) := c + r • u θ
  let L (θ r : ℝ) := fderiv ℝ W (F θ r)
  let P (θ r : ℝ) := r * planarCross (W (F θ r)) (v θ)
  let Q (θ r : ℝ) := planarCross (W (F θ r)) (u θ)
  let p (θ r : ℝ) := planarCross (W (F θ r)) (v θ) + r * planarCross (L θ r (u θ)) (v θ)
  let q (θ r : ℝ) := planarCross (L θ r (r • v θ)) (u θ) + planarCross (W (F θ r)) (v θ)
  have hL := hW.continuous_fderiv (by decide)
  have hu : Continuous u := hγ.continuous.sub continuous_const
  have hv : Continuous v := hγ.continuous_deriv_one
  have hF : Continuous F.uncurry := continuous_const.add (continuous_snd.smul (hu.comp continuous_fst))
  have hLc : Continuous L.uncurry := hL.comp hF
  have hpc : Continuous p.uncurry := by
    dsimp only [p, Function.uncurry]
    exact (continuous_planarCross (hW.continuous.comp hF) (hv.comp continuous_fst)).add
      (continuous_snd.mul (continuous_planarCross (hLc.clm_apply (hu.comp continuous_fst)) (hv.comp continuous_fst)))
  have hqc : Continuous q.uncurry := by
    dsimp only [q, Function.uncurry]
    exact (continuous_planarCross (hLc.clm_apply (continuous_snd.smul (hv.comp continuous_fst))) (hu.comp continuous_fst)).add
      (continuous_planarCross (hW.continuous.comp hF) (hv.comp continuous_fst))
  have hud (θ : ℝ) : HasDerivAt u (v θ) θ := ((hγ.differentiable (by decide)) θ).hasDerivAt.sub_const c
  have hwd (θ r : ℝ) := ((hW.differentiable (by decide)) (F θ r)).hasFDerivAt
  have hp (θ r : ℝ) : HasDerivAt (P θ) (p θ r) r := by
    have hfr : HasDerivAt (F θ) (u θ) r := by
      simpa only [F, one_smul, id_eq] using! ((hasDerivAt_id r).smul_const (u θ)).const_add c
    have h := (hasDerivAt_id r).mul (planarCross_deriv
      ((hwd θ r).comp_hasDerivAt r hfr) (hasDerivAt_const r (v θ)))
    simpa [P, p, L, planarCross, Function.comp_def, Pi.mul_def] using! h
  have hq (θ r : ℝ) : HasDerivAt (fun t => Q t r) (q θ r) θ := by
    have hfθ : HasDerivAt (fun t => F t r) (r • v θ) θ := ((hud θ).const_smul r).const_add c
    exact planarCross_deriv ((hwd θ r).comp_hasDerivAt θ hfθ) (hud θ)
  have hid (θ r : ℝ) : r * planarCross (γ θ-c) (deriv γ θ) * Shape.divergence W (F θ r) = p θ r - q θ r := by
    have hh := planarCross_trace (L θ r) (u θ) (v θ)
    change _ * _ * ((L θ r 1).re + (L θ r Complex.I).im) = _
    simp only [p, q, map_smul]
    have hscale (x y : Plane) : planarCross (r • x) y = r * planarCross x y := by
      simp [planarCross, Complex.real_smul, Complex.mul_re, Complex.mul_im]
      ring
    rw [hscale]
    change r * planarCross (u θ) (v θ) * _ = _
    linear_combination -r * hh
  have hpr (θ : ℝ) : Continuous (p θ) := hpc.comp (continuous_const.prodMk continuous_id)
  have hqr (θ : ℝ) : Continuous (q θ) := hqc.comp (continuous_const.prodMk continuous_id)
  have hqθ (r : ℝ) : Continuous (fun θ => q θ r) := hqc.comp (continuous_id.prodMk continuous_const)
  have hin (θ : ℝ) : (∫ r in (0:ℝ)..1, p θ r) = planarCross (W (γ θ)) (v θ) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hp θ r) ((hpr θ).intervalIntegrable _ _)]
    simp [P, F, u, add_comm c]
  have hside (r : ℝ) : (∫ θ in a..b, q θ r) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hq θ r) ((hqθ r).intervalIntegrable _ _)]
    simp [Q, F, u, hclosed]
  have hqi : IntegrableOn q.uncurry (uIoc a b ×ˢ uIoc 0 1) :=
    (hqc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  change (∫ θ in a..b, ∫ r in (0:ℝ)..1, _ * _ * Shape.divergence W (F θ r)) = _
  simp_rw [hid]
  simp_rw [intervalIntegral.integral_sub ((hpr _).intervalIntegrable _ _) ((hqr _).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_sub
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hpc 0 1).intervalIntegrable _ _)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hqc 0 1).intervalIntegrable _ _)]
  simp_rw [hin]
  rw [intervalIntegral_intervalIntegral_swap hqi]
  simp [hside, v]

end Torsion

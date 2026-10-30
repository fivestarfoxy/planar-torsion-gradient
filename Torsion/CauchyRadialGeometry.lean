import Torsion.CauchyBoundaryStationarity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Strict radial transversality of the actual free arc

The genuine supporting normal has positive scalar product with the free-arc
position vector. Consequently the actual argument of the boundary point
increases strictly from zero to pi, including both flat-side junctions.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The origin lies strictly on the inward side of every interior free-arc
tangent. The two opposite flat endpoints rule out equality for a nonzero
supporting functional at positive height. -/
theorem cauchySupport_origin_pos {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < cauchySupport a b φ t 0 := by
  let L := cauchySupportFunctional a b φ t
  let p := cauchyExtension φ (t : ℂ)
  have htcc := Ioo_subset_Icc_self ht
  have hnonzero : L ≠ 0 := cauchySupportFunctional_ne_zero ha hφ hα0 hα1 hodd hzero hpos hlinear htcc
  have hsupport (q : ℂ) (hq : q ∈ frontier (cauchyImage φ)) : L p ≤ L q :=
    sub_nonneg.1 (cauchySupport_nonneg_frontier ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd htcc hq)
  have h0 : L p ≤ 0 := by
    simpa only [map_zero] using hsupport 0 (zero_mem_frontier_cauchyImage (hφ.continuous hα0) hodd hzero hpos)
  have hep := cauchy_boundary_endpoints hφ hα0 hα1 hodd hzero hpos
  have hpim : p.im = height φ t := by simp [p, cauchyExtension_ofReal]
  have hY : 0 < height φ t := height_pos (hφ.continuous hα0).continuousOn hpos (abs_lt.2 ht)
  have hnegative : L p < 0 := by
    apply lt_of_le_of_ne h0
    intro heq
    have hplus := hsupport (cauchyExtension φ (1 : ℂ))
      (by simpa using cauchyExtension_ofReal_mem_frontier (hφ.continuous hα0) hodd hzero hpos 1)
    have hminus := hsupport (cauchyExtension φ (-1 : ℂ))
      (by simpa using cauchyExtension_ofReal_mem_frontier (hφ.continuous hα0) hodd hzero hpos (-1))
    have hφplus : 0 ≤ φ t * (cauchyExtension φ (1 : ℂ)).re := by
      simpa only [heq, L, cauchySupportFunctional_apply, hep.2.1, mul_zero, add_zero] using hplus
    have hφminus : 0 ≤ φ t * (cauchyExtension φ (-1 : ℂ)).re := by
      simpa only [heq, L, cauchySupportFunctional_apply, hep.1, mul_zero, add_zero] using hminus
    have hφ0 : φ t = 0 := le_antisymm
      (nonpos_of_mul_nonneg_left hφplus hep.2.2.2)
      (nonneg_of_mul_nonneg_left hφminus hep.2.2.1)
    have hvY : boundaryVelocity a b φ t * height φ t = 0 := by
      simpa only [L, cauchySupportFunctional_apply, hφ0, zero_mul, zero_add, hpim] using heq
    have hv0 := (mul_eq_zero.1 hvY).resolve_right hY.ne'
    apply hnonzero
    ext w
    simp [L, cauchySupportFunctional_apply, hφ0, hv0]
  simpa only [cauchySupport, map_zero, zero_sub] using neg_pos.2 hnegative

/-- Strict positive radial transversality for the genuine outward unit
normal of the actual convex image. -/
theorem cauchyOutwardNormal_radial_pos {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 < inner (𝕜 := ℝ) (cauchyOutwardNormal φ t) (cauchyExtension φ (t : ℂ)) := by
  have h := cauchyInwardNormal_support_identity hφ hα0 hzero hlinear (Ioo_subset_Icc_self ht) 0
  simp only [zero_sub, inner_neg_right] at h
  rw [cauchyOutwardNormal, inner_neg_left, h]
  exact div_pos (cauchySupport_origin_pos ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd ht)
    (norm_pos_iff.2 (cauchyDerivativeExtension_ne_zero_on_interval
      ha hφ hα0 hα1 hodd hzero hpos hlinear (Ioo_subset_Icc_self ht)))

/-- The actual boundary argument is continuous on the whole closed free
interval. The upper-half-plane arccos formula also covers the negative
real endpoint without crossing the argument branch cut. -/
theorem cauchy_boundary_arg_continuousOn {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    ContinuousOn (fun t : ℝ => Complex.arg (cauchyExtension φ (t : ℂ))) (Icc (-1 : ℝ) 1) := by
  have hcont := (cauchy_boundary_contDiff_one hφ hα0 hα1 hodd hzero).continuous
  have hquot : ContinuousOn (fun t : ℝ => (cauchyExtension φ (t : ℂ)).re /
      ‖cauchyExtension φ (t : ℂ)‖) (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_re.comp hcont).continuousOn.div hcont.norm.continuousOn
      (fun t _ => norm_ne_zero_iff.2 (cauchy_boundary_ne_zero hφ hα0 hα1 hodd hzero hpos t))
  apply (Real.continuous_arccos.comp_continuousOn hquot).congr
  intro t ht
  exact Complex.arg_of_im_nonneg_of_ne_zero
    (by
      have hnn := height_nonneg (profile_nonneg_Icc_of_pos_odd_zero hodd hzero hpos) t
      simpa [cauchyExtension_ofReal] using hnn)
    (cauchy_boundary_ne_zero hφ hα0 hα1 hodd hzero hpos t)

/-- The actual closed free arc has argument zero and pi at its two
junctions with the flat side. -/
theorem cauchy_boundary_arg_endpoints {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    Complex.arg (cauchyExtension φ (-1 : ℂ)) = 0 ∧
      Complex.arg (cauchyExtension φ (1 : ℂ)) = Real.pi := by
  have hep := cauchy_boundary_endpoints hφ hα0 hα1 hodd hzero hpos
  exact ⟨Complex.arg_eq_zero_iff.2 ⟨hep.2.2.1.le, hep.1⟩,
    Complex.arg_eq_pi_iff.2 ⟨hep.2.2.2, hep.2.1⟩⟩

/-- The derivative of the actual free-arc angle is its strict supporting
expression at zero divided by the squared physical radius. -/
theorem cauchy_boundary_arg_hasDerivAt {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => Complex.arg (cauchyExtension φ (s : ℂ)))
      (cauchySupport a b φ t 0 / ‖cauchyExtension φ (t : ℂ)‖ ^ 2) t := by
  have him (r : ℝ) : (cauchyExtension φ (r : ℂ)).im = height φ r := by
    simp [cauchyExtension_ofReal]
  have hposim : 0 < (cauchyExtension φ (t : ℂ)).im := by
    rw [him]
    exact height_pos (hφ.continuous hα0).continuousOn hpos (abs_lt.2 ht)
  have hslit : cauchyExtension φ (t : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inr hposim.ne')
  have hlog := (Complex.hasDerivAt_log hslit).complexToReal_fderiv.comp_hasDerivAt t
    (cauchy_boundary_hasDerivAt hφ hα0 hα1 hodd hzero t)
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlog
  have harg : HasDerivAt (fun s : ℝ => Complex.arg (cauchyExtension φ (s : ℂ)))
      (((cauchyExtension φ (t : ℂ))⁻¹ * cauchyDerivativeExtension φ (t : ℂ)).im) t := by
    simpa [Function.comp_def, Complex.imCLM_apply, Complex.log_im, smul_eq_mul] using h
  convert harg using 1
  rw [cauchy_boundary_tangent_eq hφ hα0 hzero hlinear (Ioo_subset_Icc_self ht), cauchySupport_eq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, one_mul, zero_sub, sub_zero, add_zero, zero_add,
    Complex.zero_re, Complex.zero_im, Complex.normSq_eq_norm_sq, him]
  ring

/-- The actual argument parametrizes the entire free arc strictly
increasingly, including both junctions. -/
theorem cauchy_boundary_arg_strictMonoOn {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b)
    (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x) :
    StrictMonoOn (fun t : ℝ => Complex.arg (cauchyExtension φ (t : ℂ))) (Icc (-1 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (-1 : ℝ) 1)
    (cauchy_boundary_arg_continuousOn hφ hα0 hα1 hodd hzero hpos)
  intro t ht
  have ht' : t ∈ Ioo (-1 : ℝ) 1 := by simpa only [interior_Icc] using ht
  rw [(cauchy_boundary_arg_hasDerivAt hφ hα0 hα1 hodd hzero hpos hlinear ht').deriv]
  exact div_pos (cauchySupport_origin_pos ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd ht')
    (sq_pos_of_pos (norm_pos_iff.2 (cauchy_boundary_ne_zero hφ hα0 hα1 hodd hzero hpos t)))

end Torsion.Spectral

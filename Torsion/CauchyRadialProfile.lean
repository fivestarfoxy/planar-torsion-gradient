module

public import Torsion.ContinuousProfiles
public import Torsion.CauchyRadialGeometry
public import Torsion.CauchyConformalGeometry.BoundaryGeometry
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual angular parametrization and continuous radial profile

A continuous strictly increasing interval map is a homeomorphism onto its
endpoint interval. Applied to the actual argument of the Cauchy free arc,
its inverse defines the actual continuous positive radial profile.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- A continuous strictly increasing function on a compact real interval
gives a homeomorphism onto its exact endpoint interval. -/
def monotoneIntervalHomeomorph {a b c d : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Icc a b)) (hmono : StrictMonoOn f (Icc a b))
    (hleft : f a = c) (hright : f b = d) : Icc a b ≃ₜ Icc c d := by
  let g : Icc a b → Icc c d := fun x => ⟨f x, by
    rw [← hleft, ← hright]
    exact ⟨hmono.monotoneOn (left_mem_Icc.2 hab) x.property x.property.1,
      hmono.monotoneOn x.property (right_mem_Icc.2 hab) x.property.2⟩⟩
  have hinj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact hmono.injOn x.property y.property (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective g := by
    intro θ
    have hθ : (θ : ℝ) ∈ Icc (f a) (f b) := by simpa only [hleft, hright] using θ.property
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hcont hθ
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  let e : Icc a b ≃ Icc c d := Equiv.ofBijective g ⟨hinj, hsurj⟩
  have hc : Continuous e := by
    exact (hcont.comp_continuous continuous_subtype_val (fun x => x.property)).subtype_mk _
  exact hc.homeoOfEquivCompactToT2

/-- The preceding homeomorphism has precisely the original interval
function as its forward map. -/
@[simp] theorem monotoneIntervalHomeomorph_apply {a b c d : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Icc a b)) (hmono : StrictMonoOn f (Icc a b))
    (hleft : f a = c) (hright : f b = d) (x : Icc a b) :
    (monotoneIntervalHomeomorph hab f hcont hmono hleft hright x : ℝ) = f x := rfl

section Actual

variable {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
variable (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
variable (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
variable (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
variable (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
  realCauchyBoundaryRe φ x = a * height φ x - b)
variable (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
variable (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)

/-- The actual Cauchy free arc, parametrized homeomorphically by its actual
argument through the entire closed angular interval. -/
def cauchyAngleHomeomorph : Icc (-1 : ℝ) 1 ≃ₜ ContinuousProfiles.Angle :=
  monotoneIntervalHomeomorph (by norm_num : (-1 : ℝ) ≤ 1)
    (fun t : ℝ => Complex.arg (cauchyExtension φ (t : ℂ)))
    (cauchy_boundary_arg_continuousOn hφ hα0 hα1 hodd hzero hpos)
    (cauchy_boundary_arg_strictMonoOn ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd)
    (by simpa using (cauchy_boundary_arg_endpoints hφ hα0 hα1 hodd hzero hpos).1)
    (by simpa using (cauchy_boundary_arg_endpoints hφ hα0 hα1 hodd hzero hpos).2)

local notation "H" => cauchyAngleHomeomorph ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd

@[simp] theorem cauchyAngleHomeomorph_apply (x : Icc (-1 : ℝ) 1) :
    (H x : ℝ) = Complex.arg (cauchyExtension φ ((x : ℝ) : ℂ)) := rfl

theorem cauchyAngleHomeomorph_symm_arg (θ : ContinuousProfiles.Angle) :
    Complex.arg (cauchyExtension φ ((((H).symm θ : Icc (-1 : ℝ) 1) : ℝ) : ℂ)) = (θ : ℝ) := by
  exact congrArg Subtype.val ((H).apply_symm_apply θ)

/-- The actual physical free boundary point at a given angle. -/
def cauchyRadialBoundary : C(ContinuousProfiles.Angle, ℂ) where
  toFun θ := cauchyExtension φ ((((H).symm θ : Icc (-1 : ℝ) 1) : ℝ) : ℂ)
  continuous_toFun := (cauchy_boundary_contDiff_one hφ hα0 hα1 hodd hzero).continuous.comp
    (continuous_subtype_val.comp (H).symm.continuous)

local notation "P" => cauchyRadialBoundary ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd

/-- The positive continuous radius of the actual Cauchy free arc. -/
def cauchyRadialProfile : ContinuousProfiles.Profile where
  toFun θ := ‖P θ‖
  continuous_toFun := (P).continuous.norm

local notation "R" => cauchyRadialProfile ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd

@[simp] theorem cauchyRadialBoundary_apply (θ : ContinuousProfiles.Angle) :
    P θ = cauchyExtension φ ((((H).symm θ : Icc (-1 : ℝ) 1) : ℝ) : ℂ) := rfl

@[simp] theorem cauchyRadialProfile_apply (θ : ContinuousProfiles.Angle) : R θ = ‖P θ‖ := rfl

/-- The radius is strictly positive, including both endpoint angles. -/
theorem cauchyRadialProfile_pos (θ : ContinuousProfiles.Angle) : 0 < R θ := by
  rw [cauchyRadialProfile_apply]
  apply norm_pos_iff.2
  exact cauchy_boundary_ne_zero hφ hα0 hα1 hodd hzero hpos _

/-- Every angular point is an actual frontier point. -/
theorem cauchyRadialBoundary_mem_frontier (θ : ContinuousProfiles.Angle) :
    P θ ∈ frontier (cauchyImage φ) :=
  cauchyExtension_ofReal_mem_frontier (hφ.continuous hα0) hodd hzero hpos _

/-- The constructed angular parametrization has exactly the prescribed
angle, rather than merely taking its values somewhere on the free arc. -/
theorem cauchyRadialBoundary_arg (θ : ContinuousProfiles.Angle) : (P θ).arg = (θ : ℝ) :=
  cauchyAngleHomeomorph_symm_arg ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd θ

/-- Exact polar description of the actual free-arc point. -/
theorem cauchyRadialBoundary_eq_polar (θ : ContinuousProfiles.Angle) :
    P θ = ((R θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I) := by
  rw [cauchyRadialProfile_apply,
    ← cauchyRadialBoundary_arg ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd θ]
  exact (Complex.norm_mul_exp_arg_mul_I (P θ)).symm

/-- The complete actual closed free arc is precisely the range of the
constructed angular boundary parametrization. -/
theorem range_cauchyRadialBoundary :
    range P = (fun t : ℝ => cauchyExtension φ (t : ℂ)) '' Icc (-1 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro w ⟨θ, rfl⟩
    exact ⟨((H).symm θ : ℝ), ((H).symm θ).property, rfl⟩
  · rintro w ⟨t, ht, rfl⟩
    refine ⟨H ⟨t, ht⟩, ?_⟩
    simp only [cauchyRadialBoundary_apply, (H).symm_apply_apply]

private theorem cauchyAngleHomeomorph_symm_zero :
    (H).symm ⟨0, by simp [Real.pi_pos.le]⟩ = ⟨-1, by norm_num⟩ := by
  apply (H).injective
  apply Subtype.ext
  simpa only [(H).apply_symm_apply, cauchyAngleHomeomorph_apply, Subtype.coe_mk,
    Complex.ofReal_neg, Complex.ofReal_one] using
      (cauchy_boundary_arg_endpoints hφ hα0 hα1 hodd hzero hpos).1.symm

private theorem cauchyAngleHomeomorph_symm_pi :
    (H).symm ⟨Real.pi, by simp [Real.pi_pos.le]⟩ = ⟨1, by norm_num⟩ := by
  apply (H).injective
  apply Subtype.ext
  simpa only [(H).apply_symm_apply, cauchyAngleHomeomorph_apply, Subtype.coe_mk,
    Complex.ofReal_one] using
      (cauchy_boundary_arg_endpoints hφ hα0 hα1 hodd hzero hpos).2.symm

/-- The actual radial profile includes its two prescribed endpoint radii. -/
theorem cauchyRadialProfile_endpoints :
    R ⟨0, by simp [Real.pi_pos.le]⟩ = ‖cauchyExtension φ (-1 : ℂ)‖ ∧
      R ⟨Real.pi, by simp [Real.pi_pos.le]⟩ = ‖cauchyExtension φ (1 : ℂ)‖ := by
  constructor
  · simp only [cauchyRadialProfile_apply, cauchyRadialBoundary_apply,
      cauchyAngleHomeomorph_symm_zero ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd,
      Subtype.coe_mk, Complex.ofReal_neg, Complex.ofReal_one]
  · simp only [cauchyRadialProfile_apply, cauchyRadialBoundary_apply,
      cauchyAngleHomeomorph_symm_pi ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd,
      Subtype.coe_mk, Complex.ofReal_one]

/-- Reflection makes the two endpoint radii exactly equal. -/
theorem cauchyRadialProfile_endpoints_eq :
    R ⟨0, by simp [Real.pi_pos.le]⟩ = R ⟨Real.pi, by simp [Real.pi_pos.le]⟩ := by
  rw [(cauchyRadialProfile_endpoints ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd).1,
    (cauchyRadialProfile_endpoints ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd).2]
  have h := congrArg norm (cauchy_boundary_neg_conj hφ hα0 hα1 hodd hzero (1 : ℝ))
  simpa using h

end Actual

end Torsion.Spectral

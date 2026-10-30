module

public import Torsion.CauchyTransformRealBoundary
public import Torsion.CauchyTransformImaginaryBoundary
public import Torsion.SpectralHolderCalculus

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A genuine continuous Cauchy extension to the real boundary

The real part is the proved absolutely convergent subtracted Hilbert integral;
the imaginary part is the proved fixed-kernel Poisson extension.  On the
upper half-plane their combination is the original concrete Cauchy integral.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- The actual Cauchy boundary extension for a real density. -/
def realCauchyExtension (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  (realCauchyReExtension f z : ℂ) + (poissonExtension f z : ℂ) * Complex.I

theorem realCauchyExtension_eq {f : ℝ → ℝ}
    (hf : Continuous f) (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) : realCauchyExtension f z = realCauchy f z := by
  apply Complex.ext
  · simpa [realCauchyExtension] using (realCauchyReExtension_eq_re (f := f) hz)
  · simpa [realCauchyExtension] using (realCauchy_im_eq_poissonExtension hf hzero hz).symm

theorem realCauchyExtension_ofReal (f : ℝ → ℝ) (x : ℝ) :
    realCauchyExtension f (x : ℂ) =
      (realCauchyBoundaryRe f x : ℂ) + (f x : ℂ) * Complex.I := by
  simp only [realCauchyExtension, realCauchyReExtension_ofReal, poissonExtension_ofReal]

/-- Both boundary components are proved jointly continuous, including the
support endpoints. -/
theorem realCauchyExtension_continuousOn {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) :
    ContinuousOn (realCauchyExtension f) (closure upperHalfPlane) := by
  exact (Complex.continuous_ofReal.comp_continuousOn
    (realCauchyReExtension_continuousOn_closure hf hα hzero)).add
      ((Complex.continuous_ofReal.comp
        (poissonExtension_continuous (hf.continuous hα) hzero)).continuousOn.mul continuousOn_const)

theorem realCauchy_differentiableOn {f : ℝ → ℝ} (hf : Continuous f) :
    DifferentiableOn ℂ (realCauchy f) upperHalfPlane := by
  exact (differentiableOn_cauchy_integral
    (Complex.continuous_ofReal.comp hf).continuousOn).const_mul (-((Real.pi : ℂ)⁻¹))

/-- The proved extension supplies precisely the closed-boundary holomorphic
object required by the half-plane uniqueness theorem. -/
theorem realCauchyExtension_diffContOnCl {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) :
    DiffContOnCl ℂ (realCauchyExtension f) upperHalfPlane := by
  refine ⟨?_, realCauchyExtension_continuousOn hf hα hzero⟩
  exact (realCauchy_differentiableOn (hf.continuous hα)).congr
    (fun z hz => realCauchyExtension_eq (hf.continuous hα) hzero hz)

/-- The complete complex boundary limit permits arbitrary approach through
the upper half-plane, rather than merely vertical approach. -/
theorem realCauchy_boundary_tendsto {f : ℝ → ℝ} {C α : ℝ≥0}
    (hf : HolderWith C α f) (hα : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → f s = 0) (x : ℝ) :
    Tendsto (realCauchy f) (𝓝[upperHalfPlane] (x : ℂ))
      (𝓝 ((realCauchyBoundaryRe f x : ℂ) + (f x : ℂ) * Complex.I)) := by
  have h := (realCauchyExtension_diffContOnCl hf hα hzero).continuousOn
  have hx : (x : ℂ) ∈ closure upperHalfPlane := by
    apply mem_closure_iff_nhdsWithin_neBot.mpr
    have hpath : Tendsto (fun c : ℝ => (x : ℂ) + (c⁻¹ : ℝ) * Complex.I) atTop (𝓝 (x : ℂ)) := by
      have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
      simpa using (tendsto_const_nhds.add (h.mul_const Complex.I))
    have him : ∀ᶠ c : ℝ in atTop,
        (x : ℂ) + (c⁻¹ : ℝ) * Complex.I ∈ upperHalfPlane := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
      simpa [upperHalfPlane] using inv_pos.2 hc
    exact (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hpath him).neBot
  have hlim := (h (x : ℂ) hx).mono subset_closure
  change Tendsto (realCauchyExtension f) (𝓝[upperHalfPlane] (x : ℂ))
    (𝓝 (realCauchyExtension f (x : ℂ))) at hlim
  rw [realCauchyExtension_ofReal] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact realCauchyExtension_eq (hf.continuous hα) hzero hz

/-- Continuous closed-half-plane extension of the spectral Cauchy map. -/
def cauchyExtension (φ : ℝ → ℝ) : ℂ → ℂ := realCauchyExtension (height φ)

/-- The actual derivative extension, obtained from the proved Cauchy
integration-by-parts identity. -/
def cauchyDerivativeExtension (φ : ℝ → ℝ) (z : ℂ) : ℂ := -realCauchyExtension φ z

/-- The actual auxiliary derivative extension, with density Yφ. -/
def auxiliaryDerivativeExtension (φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  -realCauchyExtension (fun s => height φ s * φ s) z

theorem cauchyExtension_eq {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    cauchyExtension φ z = cauchy φ z := by
  exact realCauchyExtension_eq (height_continuous hφ)
    (fun _ hs => height_zero_of_one_le_abs φ hs) hz

theorem cauchyDerivativeExtension_eq {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    cauchyDerivativeExtension φ z = deriv (cauchy φ) z := by
  rw [cauchyDerivativeExtension, realCauchyExtension_eq hφ hzero hz,
    deriv_cauchy_eq_eigenfunction_integral hφ hodd hzero hz]
  simp [realCauchy]

theorem auxiliaryDerivativeExtension_eq {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    auxiliaryDerivativeExtension φ z = deriv (auxiliary φ) z := by
  rw [auxiliaryDerivativeExtension, realCauchyExtension_eq
    (f := fun s => height φ s * φ s)
    (by simpa only [Pi.mul_apply] using! (height_continuous hφ.continuousOn).mul hφ)
    (fun s hs => by rw [height_zero_of_one_le_abs φ hs, zero_mul]) hz,
    deriv_auxiliary_eq_product_integral hφ hodd hzero hz]
  simp [realCauchy]

theorem cauchyDerivativeExtension_ofReal (φ : ℝ → ℝ) (x : ℝ) :
    cauchyDerivativeExtension φ (x : ℂ) =
      -(realCauchyBoundaryRe φ x : ℂ) - (φ x : ℂ) * Complex.I := by
  rw [cauchyDerivativeExtension, realCauchyExtension_ofReal]
  ring

theorem cauchyExtension_ofReal (φ : ℝ → ℝ) (x : ℝ) :
    cauchyExtension φ (x : ℂ) =
      (realCauchyBoundaryRe (height φ) x : ℂ) + (height φ x : ℂ) * Complex.I :=
  realCauchyExtension_ofReal (height φ) x

theorem cauchyExtension_diffContOnCl {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hY : HolderWith C α (height φ)) (hα : 0 < α) :
    DiffContOnCl ℂ (cauchyExtension φ) upperHalfPlane :=
  realCauchyExtension_diffContOnCl hY hα
    (fun _ hs => height_zero_of_one_le_abs φ hs)

theorem cauchyDerivativeExtension_diffContOnCl {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα : 0 < α)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) :
    DiffContOnCl ℂ (cauchyDerivativeExtension φ) upperHalfPlane :=
  ⟨(realCauchyExtension_diffContOnCl hφ hα hzero).differentiableOn.neg,
    (realCauchyExtension_diffContOnCl hφ hα hzero).continuousOn.neg⟩

theorem auxiliaryDerivativeExtension_diffContOnCl {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hYφ : HolderWith C α (fun s => height φ s * φ s)) (hα : 0 < α) :
    DiffContOnCl ℂ (auxiliaryDerivativeExtension φ) upperHalfPlane := by
  have h := realCauchyExtension_diffContOnCl hYφ hα
    (fun s hs => by rw [height_zero_of_one_le_abs φ hs, zero_mul])
  exact ⟨h.differentiableOn.neg, h.continuousOn.neg⟩


theorem auxiliaryDerivativeExtension_ofReal (φ : ℝ → ℝ) (x : ℝ) :
    auxiliaryDerivativeExtension φ (x : ℂ) =
      -(realCauchyBoundaryRe (fun s => height φ s * φ s) x : ℂ) -
        (height φ x * φ x : ℝ) * Complex.I := by
  rw [auxiliaryDerivativeExtension, realCauchyExtension_ofReal]
  ring

/-- Continuous closed-half-plane extension of the auxiliary transform. -/
def auxiliaryExtension (φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * realCauchyExtension (fun s => (height φ s) ^ 2) z

theorem auxiliaryExtension_eq {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    auxiliaryExtension φ z = auxiliary φ z := by
  rw [auxiliaryExtension, realCauchyExtension_eq
    (f := fun s => (height φ s) ^ 2)
    (by simpa only [Pi.pow_apply] using! (height_continuous hφ).pow 2)
    (fun s hs => by rw [height_zero_of_one_le_abs φ hs]; norm_num) hz]
  unfold realCauchy auxiliary
  simp only [mul_inv_rev]
  ring

theorem auxiliaryExtension_ofReal (φ : ℝ → ℝ) (x : ℝ) :
    auxiliaryExtension φ (x : ℂ) =
      (1 / 2 : ℂ) * (realCauchyBoundaryRe (fun s => (height φ s) ^ 2) x : ℂ) +
        ((height φ x) ^ 2 / 2 : ℝ) * Complex.I := by
  rw [auxiliaryExtension, realCauchyExtension_ofReal]
  push_cast
  ring

theorem auxiliaryExtension_diffContOnCl {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hYsq : HolderWith C α (fun s => (height φ s) ^ 2)) (hα : 0 < α) :
    DiffContOnCl ℂ (auxiliaryExtension φ) upperHalfPlane := by
  have h := realCauchyExtension_diffContOnCl hYsq hα
    (fun s hs => by rw [height_zero_of_one_le_abs φ hs]; norm_num)
  exact ⟨h.differentiableOn.const_mul _, continuousOn_const.mul h.continuousOn⟩

/-- All four concrete transforms admit genuine continuous holomorphic
closed-half-plane extensions from the original single Hölder input.  The
regularity of Y, Y² and Yφ is proved by the preceding density calculus. -/
theorem cauchy_extensions_diffContOnCl_of_holder {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) :
    DiffContOnCl ℂ (cauchyExtension φ) upperHalfPlane ∧
      DiffContOnCl ℂ (cauchyDerivativeExtension φ) upperHalfPlane ∧
      DiffContOnCl ℂ (auxiliaryExtension φ) upperHalfPlane ∧
      DiffContOnCl ℂ (auxiliaryDerivativeExtension φ) upperHalfPlane := by
  obtain ⟨CY, hY⟩ := height_exists_holder (hφ.continuous hα0) hodd hzero hα1
  obtain ⟨CYφ, hYφ⟩ := height_mul_exists_holder hφ hα0 hα1 hodd hzero
  obtain ⟨BY, hBY⟩ := exists_nnreal_bound_of_compactSupport
    (height_continuous (hφ.continuous hα0).continuousOn) (height_hasCompactSupport φ)
  have hYsq : HolderWith (BY * CY + BY * CY) α (fun s => (height φ s) ^ 2) := by
    simpa only [pow_two] using holderWith_mul_of_bounded hY hY hBY hBY
  exact ⟨cauchyExtension_diffContOnCl hY hα0,
    cauchyDerivativeExtension_diffContOnCl hφ hα0 hzero,
    auxiliaryExtension_diffContOnCl hYsq hα0,
    auxiliaryDerivativeExtension_diffContOnCl hYφ hα0⟩

end Torsion.Spectral



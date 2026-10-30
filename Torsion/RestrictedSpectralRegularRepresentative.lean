module

public import Torsion.RestrictedSpectralWeakPrimitive
public import Torsion.RestrictedSpectralHeightParity
public import Torsion.RestrictedSpectralAnalyticHeight
public import Torsion.RestrictedSpectralSignRegularity
public import Torsion.RestrictedSpectralOddPositivity
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The actual regular representative of an odd restricted eigenfunction

The concrete negative derivative of the original height, set to zero
outside the interval, is identified with the original L² datum by local
classical integration by parts and separation by genuine smooth tests.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- The concrete regular representative extracted from the actual height. -/
def regularEigenfunction (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if |x| < 1 then -deriv (height f) x else 0

theorem regularEigenfunction_zero_exterior (f : ℝ → ℝ) (x : ℝ) (hx : 1 ≤ |x|) :
    regularEigenfunction f x = 0 := by
  simp only [regularEigenfunction, if_neg (not_lt.2 hx)]

theorem regularEigenfunction_odd (f : ℝ → ℝ) : Function.Odd (regularEigenfunction f) :=
  piecewise_neg_deriv_height_odd f

/-- A local C¹ function times a smooth test supported in the open region
is globally C¹, since the test vanishes in a neighborhood of every point
outside the region. -/
theorem contDiff_mul_of_tsupport_subset {H ψ : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hH : ContDiffOn ℝ 1 H U) (hψ : ContDiff ℝ 1 ψ)
    (hsupp : tsupport ψ ⊆ U) : ContDiff ℝ 1 (fun x => H x * ψ x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hH.contDiffAt (hU.mem_nhds hx)).mul hψ.contDiffAt
  · have hn : x ∉ tsupport ψ := fun h => hx (hsupp h)
    have hz : ψ =ᶠ[𝓝 x] 0 := not_mem_tsupport_iff_eventuallyEq.1 hn
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]

/-- Local continuity likewise suffices after multiplication by a
continuous compactly supported test inside the region. -/
theorem continuous_mul_of_tsupport_subset {H ψ : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hH : ContinuousOn H U) (hψ : Continuous ψ)
    (hsupp : tsupport ψ ⊆ U) : Continuous (fun x => H x * ψ x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hH.continuousAt (hU.mem_nhds hx)).mul hψ.continuousAt
  · have hn : x ∉ tsupport ψ := fun h => hx (hsupp h)
    have hz : ψ =ᶠ[𝓝 x] 0 := not_mem_tsupport_iff_eventuallyEq.1 hn
    apply (show ContinuousAt (fun _ : ℝ => (0 : ℝ)) x from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]

/-- Classical integration by parts requires only C¹ regularity on the
open region containing the actual test support. -/
theorem integral_mul_deriv_eq_neg_deriv_mul_of_local_contDiff
    {H ψ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hH : ContDiffOn ℝ 1 H U) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ U) :
    (∫ x : ℝ, H x * deriv ψ x) = -(∫ x : ℝ, deriv H x * ψ x) := by
  let P : ℝ → ℝ := fun x => H x * ψ x
  have hP : ContDiff ℝ 1 P := contDiff_mul_of_tsupport_subset hU hH (hψ.of_le (by simp)) hsupp
  have hPc : HasCompactSupport P := hc.mul_left
  have hPderiv : ∫ x : ℝ, deriv P x = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable
      (fun x => ((hP.differentiable (by simp)) x).hasDerivAt)
      ((hP.continuous_deriv le_rfl).integrable_of_hasCompactSupport hPc.deriv)
      (hP.continuous.integrable_of_hasCompactSupport hPc)
  have hHi : Integrable (fun x : ℝ => deriv H x * ψ x) :=
    (continuous_mul_of_tsupport_subset hU
      (hH.continuousOn_deriv_of_isOpen hU le_rfl) hψ.continuous hsupp).integrable_of_hasCompactSupport hc.mul_left
  have hHψi : Integrable (fun x : ℝ => H x * deriv ψ x) :=
    (continuous_mul_of_tsupport_subset hU hH.continuousOn
      (hψ.continuous_deriv (by simp)) ((closure_minimal support_deriv_subset (isClosed_tsupport ψ)).trans hsupp)).integrable_of_hasCompactSupport hc.deriv.mul_left
  have hpoint (x : ℝ) : deriv P x = deriv H x * ψ x + H x * deriv ψ x := by
    by_cases hx : x ∈ U
    · exact deriv_mul ((hH.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
        (hψ.differentiable (by simp) x)
    · have hn : x ∉ tsupport ψ := fun h => hx (hsupp h)
      have hnP : x ∉ tsupport P := fun h => hn (tsupport_mul_subset_right h)
      simp only [deriv, fderiv_of_not_mem_tsupport ℝ hnP, fderiv_of_not_mem_tsupport ℝ hn,
        ContinuousLinearMap.zero_apply, image_eq_zero_of_notMem_tsupport hn, mul_zero, zero_mul, add_zero]
  rw [show (deriv P) = (fun x => deriv H x * ψ x + H x * deriv ψ x) from funext hpoint,
    integral_add hHi hHψi] at hPderiv
  linarith

/-- A locally C¹ weak primitive has the actual datum as its negative
classical derivative almost everywhere on its open region. -/
theorem ae_neg_deriv_eq_of_weak_primitive {H f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hH : ContDiffOn ℝ 1 H U) (hf : LocallyIntegrableOn f U volume)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ x : ℝ, H x * deriv ψ x) = ∫ x : ℝ, f x * ψ x) :
    ∀ᵐ x : ℝ ∂volume, x ∈ U → -deriv H x = f x := by
  have hd : LocallyIntegrableOn (fun x => -deriv H x - f x) U volume :=
    ((hH.continuousOn_deriv_of_isOpen hU le_rfl).neg.locallyIntegrableOn hU.measurableSet).sub hf
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hd (by
    intro ψ hψ hc hsupp
    have hibp := integral_mul_deriv_eq_neg_deriv_mul_of_local_contDiff hU hH hψ hc hsupp
    have hw := hweak ψ hψ hc hsupp
    have hdi : Integrable (fun x => deriv H x * ψ x) :=
      (continuous_mul_of_tsupport_subset hU (hH.continuousOn_deriv_of_isOpen hU le_rfl)
        hψ.continuous hsupp).integrable_of_hasCompactSupport hc.mul_left
    have hfi : Integrable (fun x => f x * ψ x) := by
      have hloc := hf.integrableOn_compact_subset hsupp hc
      apply (integrableOn_iff_integrable_of_support_subset ?_).1
        (hloc.mul_continuousOn hψ.continuous.continuousOn hc)
      intro x hx
      apply subset_tsupport ψ
      contrapose! hx
      simp only [Function.mem_support, not_not] at hx ⊢
      simp [hx]
    simp only [smul_eq_mul, mul_sub, mul_neg]
    simp_rw [mul_comm (ψ _) (deriv H _), mul_comm (ψ _) (f _)]
    have hneg : Integrable (fun x => -(deriv H x * ψ x)) := hdi.neg
    rw [integral_sub hneg hfi, integral_neg]
    linarith)
  filter_upwards [hz] with x hx hxi
  exact sub_eq_zero.1 (hx hxi)


/-- When the original concrete height is C¹ inside the interval, its
zero-exterior negative classical derivative represents the actual datum. -/
theorem MemRestrictedFormDomain.regularEigenfunction_ae_eq_of_contDiff
    {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f)
    (hY : ContDiffOn ℝ 1 (height f) (Ioo (-1 : ℝ) 1)) :
    regularEigenfunction f =ᵐ[volume] f := by
  have hinside := ae_neg_deriv_eq_of_weak_primitive isOpen_Ioo hY
    (hf.integrable.locallyIntegrable.locallyIntegrableOn (Ioo (-1 : ℝ) 1))
    (fun ψ hψ hc _ => hf.integral_height_mul_deriv hodd hψ hc)
  filter_upwards [hinside, hf.2.2.1] with x hx hz
  by_cases hxi : |x| < 1
  · rw [regularEigenfunction, if_pos hxi]
    exact hx (abs_lt.1 hxi)
  · rw [regularEigenfunction, if_neg hxi]
    exact (hz (fun hi => hxi (abs_lt.2 hi))).symm

/-- The regular representative of an actual odd weak eigenfunction is in
the original a.e. class, using the constructed analytic height theorem. -/
theorem IsRestrictedEigenfunction.regularEigenfunction_ae_eq
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f) :
    regularEigenfunction f =ᵐ[volume] f := by
  apply hf.1.regularEigenfunction_ae_eq_of_contDiff hodd
  exact (hf.height_analyticOnNhd_of_odd hodd).contDiffOn isOpen_Ioo.uniqueDiffOn

/-- The constructed regular representative satisfies the original weak
restricted eigenfunction equation, rather than a replacement equation. -/
theorem IsRestrictedEigenfunction.regularEigenfunction_isRestrictedEigenfunction
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f) :
    IsRestrictedEigenfunction a (regularEigenfunction f) :=
  hf.congr_ae (hf.regularEigenfunction_ae_eq hodd).symm

/-- The original height itself is unchanged by passing to the actual
regular representative. -/
theorem IsRestrictedEigenfunction.height_regularEigenfunction
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f) :
    height (regularEigenfunction f) = height f := by
  funext x
  unfold height
  split_ifs
  · exact integral_congr_ae (ae_restrict_of_ae (hf.regularEigenfunction_ae_eq hodd))
  · rfl


/-- The concrete representative is genuinely real analytic at every
interior point of the original spectral interval. -/
theorem IsRestrictedEigenfunction.regularEigenfunction_analyticAt
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    AnalyticAt ℝ (regularEigenfunction f) x := by
  apply ((hf.height_analyticAt_of_odd hodd x hx).deriv.neg).congr
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  simp only [regularEigenfunction, if_pos (abs_lt.2 hy), Pi.neg_apply]

/-- The constructed representative is analytic on a neighborhood of
every point in the entire open spectral interval, including the origin. -/
theorem IsRestrictedEigenfunction.regularEigenfunction_analyticOnNhd
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f) :
    AnalyticOnNhd ℝ (regularEigenfunction f) (Ioo (-1 : ℝ) 1) :=
  fun x hx => hf.regularEigenfunction_analyticAt hodd x hx

/-- Interior smoothness is obtained from the actual analytic construction. -/
theorem IsRestrictedEigenfunction.regularEigenfunction_contDiffOn
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f) :
    ContDiffOn ℝ ∞ (regularEigenfunction f) (Ioo (-1 : ℝ) 1) :=
  (hf.regularEigenfunction_analyticOnNhd hodd).contDiffOn isOpen_Ioo.uniqueDiffOn

/-- Passing to the representative a second time gives exactly the same
pointwise function, since the concrete integrated height is unchanged. -/
theorem IsRestrictedEigenfunction.regularEigenfunction_idempotent
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f) :
    regularEigenfunction (regularEigenfunction f) = regularEigenfunction f := by
  funext x
  change (if |x| < 1 then -deriv (height (regularEigenfunction f)) x else 0) = _
  rw [hf.height_regularEigenfunction hodd]
  rfl

/-- The nonnegative a.e. half-line sign becomes pointwise nonnegativity
of the actual analytic representative on the positive interval. -/
theorem IsRestrictedEigenfunction.regularEigenfunction_nonneg
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f) :
    ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ regularEigenfunction f x := by
  apply nonneg_on_Ioo_of_continuousOn_ae_nonneg
    ((hf.regularEigenfunction_contDiffOn hodd).continuousOn.mono (fun _ hx => ⟨by linarith [hx.1], hx.2⟩))
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f :=
    ae_restrict_of_ae_restrict_of_subset (fun _ hx => hx.1) hnonneg
  filter_upwards [ae_restrict_of_ae (hf.regularEigenfunction_ae_eq hodd), hnn] with x hx hn
  rw [hx]
  exact hn

/-- Least-odd strict a.e. positivity is preserved by the genuine analytic
representative. This does not infer strict pointwise positivity merely
from analyticity. -/
theorem IsRestrictedEigenfunction.regularEigenfunction_pos_ae
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hlower : ∀ v : ℝ → ℝ, MemRestrictedFormDomain v → Function.Odd v →
      a * (∫ x : ℝ, v x ^ 2) ≤ energy v v)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f) :
    ∀ᵐ x : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < regularEigenfunction f x := by
  filter_upwards [ae_restrict_of_ae (hf.regularEigenfunction_ae_eq hodd),
    hf.pos_ae_of_odd_rayleigh_lower_bound hodd hlower hnonneg] with x hx hp
  rw [hx]
  exact hp

end Torsion.Spectral

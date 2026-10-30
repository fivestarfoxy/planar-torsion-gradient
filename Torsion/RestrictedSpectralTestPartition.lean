module

public import Torsion.RestrictedSpectralDistribution
public import Torsion.RestrictedSpectralEndpointCutoffBasic
public import Torsion.RestrictedSpectralEndpointCutoffs
public import Torsion.RestrictedSpectralSchwartz

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual interior and exterior test partition away from the endpoints

An actual smooth test which vanishes near both marked endpoints splits
into a genuine original restricted core test and an exterior test. The
interior piece is the literal interval restriction, whose smoothness and
compact support follow from the proved endpoint gap.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff SchwartzMap

namespace Torsion.Spectral

/-- Literal interior restriction of the original real test. -/
def interiorTestPart (ψ : ℝ → ℝ) : ℝ → ℝ := (Ioo (-1 : ℝ) 1).indicator ψ

/-- The remaining actual exterior part. -/
def exteriorTestPart (ψ : ℝ → ℝ) (x : ℝ) : ℝ := ψ x - interiorTestPart ψ x

/-- Endpoint vanishing puts the actual interior restriction's support
strictly inside the original interval. -/
theorem tsupport_interiorTestPart_subset {ψ : ℝ → ℝ} {ε : ℝ} (_hε : 0 < ε)
    (hgap : ∀ x : ℝ, |x - 1| < ε ∨ |x + 1| < ε → ψ x = 0) :
    tsupport (interiorTestPart ψ) ⊆ Icc (-1 + ε) (1 - ε) := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  have hxi : x ∈ Ioo (-1 : ℝ) 1 := by
    by_contra hn
    exact hx (by simp only [interiorTestPart, indicator_of_notMem hn])
  have hψne : ψ x ≠ 0 := by simpa only [Function.mem_support, interiorTestPart, indicator_of_mem hxi] using hx
  have hr : ε ≤ |x - 1| := le_of_not_gt (fun h => hψne (hgap x (Or.inl h)))
  have hl : ε ≤ |x + 1| := le_of_not_gt (fun h => hψne (hgap x (Or.inr h)))
  rw [abs_of_neg (sub_neg.2 hxi.2)] at hr
  rw [abs_of_pos (by linarith [hxi.1] : 0 < x + 1)] at hl
  constructor <;> linarith

/-- The endpoint gap makes the literal interior piece a genuine core
function of the original restricted form, with no new test notion. -/
theorem interiorTestPart_isCore {ψ : ℝ → ℝ} {ε : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hε : 0 < ε)
    (hgap : ∀ x : ℝ, |x - 1| < ε ∨ |x + 1| < ε → ψ x = 0) :
    IsCore (interiorTestPart ψ) := by
  have hsupport := tsupport_interiorTestPart_subset hε hgap
  have hinside : tsupport (interiorTestPart ψ) ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx
    have hi := hsupport hx
    constructor <;> linarith [hi.1, hi.2]
  refine ⟨?_, isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsupport, hinside⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · apply hψ.contDiffAt.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact indicator_of_mem hy ψ
  · have hn : x ∉ tsupport (interiorTestPart ψ) := fun h => hx (hinside h)
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.1 hn)

/-- The exterior part actually vanishes on a larger interval containing
the entire closed source interval. -/
theorem exteriorTestPart_zero_of_abs_lt {ψ : ℝ → ℝ} {ε : ℝ} (_hε : 0 < ε)
    (hgap : ∀ x : ℝ, |x - 1| < ε ∨ |x + 1| < ε → ψ x = 0)
    {x : ℝ} (hx : |x| < 1 + ε) : exteriorTestPart ψ x = 0 := by
  by_cases hxi : |x| < 1
  · change ψ x - (Ioo (-1 : ℝ) 1).indicator ψ x = 0
    have hmem : x ∈ Ioo (-1 : ℝ) 1 := abs_lt.1 hxi
    rw [indicator_of_mem hmem, sub_self]
  · have hnot : x ∉ Ioo (-1 : ℝ) 1 := fun h => hxi (abs_lt.2 h)
    rw [exteriorTestPart, interiorTestPart, indicator_of_notMem hnot, sub_zero]
    apply hgap x
    rcases le_total 0 x with hx0 | hx0
    · left
      rw [abs_of_nonneg hx0] at hx
      have hx1 : 1 ≤ x := le_of_not_gt (fun h => hxi (by rw [abs_of_nonneg hx0]; exact h))
      rw [abs_of_nonneg (by linarith : 0 ≤ x - 1)]
      linarith
    · right
      rw [abs_of_nonpos hx0] at hx
      have hx1 : x ≤ -1 := by
        have h : 1 ≤ |x| := le_of_not_gt hxi
        rw [abs_of_nonpos hx0] at h
        linarith
      rw [abs_of_nonpos (by linarith : x + 1 ≤ 0)]
      linarith

/-- The partition is the original test pointwise. -/
theorem interiorTestPart_add_exteriorTestPart (ψ : ℝ → ℝ) (x : ℝ) :
    interiorTestPart ψ x + exteriorTestPart ψ x = ψ x := by
  unfold exteriorTestPart
  ring

/-- Multiplication against a shrinking uniformly bounded endpoint piece
vanishes for every actual L¹ density. This permits endpoint-singular L¹
residuals and does not rely on a pointwise bound for the density. -/
theorem integral_mul_tendsto_zero_of_shrinking_support
    {q : ℝ → ℝ} {w : ℕ → ℝ → ℝ} {M e : ℝ}
    (hq : Integrable q) (hwm : ∀ n, AEStronglyMeasurable (w n) volume)
    (hbound : ∀ n x, |w n x| ≤ M)
    (hzero : ∀ x : ℝ, x ≠ e → ∀ᶠ n : ℕ in atTop, w n x = 0) :
    Tendsto (fun n => ∫ x : ℝ, q x * w n x) atTop (𝓝 0) := by
  have hM : 0 ≤ M := (abs_nonneg (w 0 0)).trans (hbound 0 0)
  have hdom : Integrable (fun x : ℝ => M * ‖q x‖) := hq.norm.const_mul M
  have hm (n : ℕ) : AEStronglyMeasurable (fun x : ℝ => q x * w n x) volume :=
    hq.aestronglyMeasurable.mul (hwm n)
  have hb : ∀ n, ∀ᵐ x : ℝ, ‖q x * w n x‖ ≤ M * ‖q x‖ := fun n => ae_of_all _ fun x => by
    rw [norm_mul, Real.norm_eq_abs (w n x)]
    nlinarith [hbound n x, norm_nonneg (q x)]
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ e := by
    simp only [ae_iff, not_not, setOf_eq_eq_singleton, measure_singleton]
  have hp : ∀ᵐ x : ℝ, Tendsto (fun n => q x * w n x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hne] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hzero x hx] with n hn
    simp only [hn, mul_zero]
  have h := tendsto_integral_of_dominated_convergence (fun x => M * ‖q x‖) hm hdom hb hp
  simpa only [integral_zero] using h


/-- Removing the two actual endpoint localizations leaves a real smooth
test with a genuine neighborhood gap at each endpoint. The index shift
ensures that the two endpoint bumps have disjoint plateau neighborhoods. -/
def endpointTrim (ψ : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ψ x - endpointCutoff ψ 1 (n + 3) x - endpointCutoff ψ (-1) (n + 3) x

theorem endpointTrim_contDiff {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (n : ℕ) :
    ContDiff ℝ ∞ (endpointTrim ψ n) :=
  (hψ.sub (endpointCutoff_contDiff hψ 1 (n + 3))).sub
    (endpointCutoff_contDiff hψ (-1) (n + 3))

theorem endpointTrim_eq_zero_near_endpoints (ψ : ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hx : |x - 1| < 1 / endpointCutoffScale (n + 3) ∨
      |x + 1| < 1 / endpointCutoffScale (n + 3)) : endpointTrim ψ n x = 0 := by
  have hN : 4 ≤ endpointCutoffScale (n + 3) := by
    unfold endpointCutoffScale
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hNpos := endpointCutoffScale_pos (n + 3)
  have hr : 1 / endpointCutoffScale (n + 3) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num) hN
  have hR : 2 / endpointCutoffScale (n + 3) ≤ 1 / 2 := by
    exact (div_le_iff₀ hNpos).2 (by linarith)
  unfold endpointTrim
  rcases hx with hx | hx
  · rw [endpointCutoff_eq_self ψ 1 (n + 3) hx.le]
    have hfar : 2 / endpointCutoffScale (n + 3) ≤ |x - (-1)| := by
      have hxx := (abs_lt.1 (hx.trans_le hr)).1
      have hbound : 1 / 2 ≤ |x + 1| := by nlinarith [le_abs_self (x + 1)]
      simpa only [sub_neg_eq_add] using hR.trans hbound
    rw [endpointCutoff_eq_zero ψ (-1) (n + 3) hfar]
    ring
  · have heq : |x - (-1)| ≤ 1 / endpointCutoffScale (n + 3) := by simpa only [sub_neg_eq_add] using hx.le
    rw [endpointCutoff_eq_self ψ (-1) (n + 3) heq]
    have hfar : 2 / endpointCutoffScale (n + 3) ≤ |x - 1| := by
      have hxx := (abs_lt.1 (hx.trans_le hr)).2
      have hbound : 1 / 2 ≤ |x - 1| := by nlinarith [neg_le_abs (x - 1)]
      exact hR.trans hbound
    rw [endpointCutoff_eq_zero ψ 1 (n + 3) hfar]
    ring

/-- Every actual endpoint-trimmed smooth test has an original interior
core component, with no unproved support or regularity premise. -/
theorem interiorTestPart_endpointTrim_isCore {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (n : ℕ) : IsCore (interiorTestPart (endpointTrim ψ n)) :=
  interiorTestPart_isCore (endpointTrim_contDiff hψ n)
    (one_div_pos.2 (endpointCutoffScale_pos (n + 3)))
    (endpointTrim_eq_zero_near_endpoints ψ n)


/-- The actual endpoint bump never increases the datum's absolute value. -/
theorem abs_endpointCutoff_le (ψ : ℝ → ℝ) (e : ℝ) (n : ℕ) (x : ℝ) :
    |endpointCutoff ψ e n x| ≤ |ψ x| := by
  rw [endpointCutoff, abs_mul, abs_of_nonneg endpointCutoffBump.nonneg]
  exact mul_le_of_le_one_right (abs_nonneg _) endpointCutoffBump.le_one

/-- Actual endpoint cutoffs vanish against every L¹ density, including
the actual possibly singular integrable exterior residual. -/
theorem integral_mul_endpointCutoff_tendsto_zero {q : ℝ → ℝ}
    (hq : Integrable q) (S : 𝓢(ℝ, ℝ)) (e : ℝ) :
    Tendsto (fun n => ∫ x : ℝ, q x * endpointCutoff S e n x) atTop (𝓝 0) := by
  apply integral_mul_tendsto_zero_of_shrinking_support hq
    (fun n => (endpointCutoff_contDiff S.smooth' e n).continuous.aestronglyMeasurable)
    (fun n x => (abs_endpointCutoff_le S e n x).trans (schwartz_uniform_bound S x))
  exact fun x hx => endpointCutoff_eventually_eq_zero S e hx

/-- The smooth endpoint-trimmed datum as an actual real Schwartz map. -/
def endpointTrimSchwartz (S : 𝓢(ℝ, ℝ)) (n : ℕ) : 𝓢(ℝ, ℝ) :=
  S - compactSmoothRealSchwartz (endpointCutoff_contDiff S.smooth' 1 (n + 3))
      (endpointCutoff_hasCompactSupport S 1 (n + 3)) -
    compactSmoothRealSchwartz (endpointCutoff_contDiff S.smooth' (-1) (n + 3))
      (endpointCutoff_hasCompactSupport S (-1) (n + 3))

@[simp] theorem endpointTrimSchwartz_apply (S : 𝓢(ℝ, ℝ)) (n : ℕ) (x : ℝ) :
    endpointTrimSchwartz S n x = endpointTrim S n x := rfl

/-- The actual interior component of an endpoint-trimmed Schwartz test. -/
def interiorTrimSchwartz (S : 𝓢(ℝ, ℝ)) (n : ℕ) : 𝓢(ℝ, ℝ) :=
  compactSmoothRealSchwartz (interiorTestPart_endpointTrim_isCore S.smooth' n).1
    (interiorTestPart_endpointTrim_isCore S.smooth' n).2.1

@[simp] theorem interiorTrimSchwartz_apply (S : 𝓢(ℝ, ℝ)) (n : ℕ) (x : ℝ) :
    interiorTrimSchwartz S n x = interiorTestPart (endpointTrim S n) x := rfl

/-- The actual exterior component remains a genuine real Schwartz map. -/
def exteriorTrimSchwartz (S : 𝓢(ℝ, ℝ)) (n : ℕ) : 𝓢(ℝ, ℝ) :=
  endpointTrimSchwartz S n - interiorTrimSchwartz S n

@[simp] theorem exteriorTrimSchwartz_apply (S : 𝓢(ℝ, ℝ)) (n : ℕ) (x : ℝ) :
    exteriorTrimSchwartz S n x = exteriorTestPart (endpointTrim S n) x := rfl

/-- The exterior Schwartz component is genuinely separated from the
entire closed source interval by its explicit positive cutoff radius. -/
theorem exteriorTrimSchwartz_gap (S : 𝓢(ℝ, ℝ)) (n : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < 1 + δ → exteriorTrimSchwartz S n x = 0 := by
  refine ⟨1 / endpointCutoffScale (n + 3), one_div_pos.2 (endpointCutoffScale_pos _), ?_⟩
  intro x hx
  exact exteriorTestPart_zero_of_abs_lt (one_div_pos.2 (endpointCutoffScale_pos _))
    (endpointTrim_eq_zero_near_endpoints S n) hx

/-- The partition reconstructs the literal trimmed test pointwise. -/
theorem interiorTrimSchwartz_add_exteriorTrimSchwartz (S : 𝓢(ℝ, ℝ)) (n : ℕ) (x : ℝ) :
    interiorTrimSchwartz S n x + exteriorTrimSchwartz S n x = endpointTrim S n x := by
  exact interiorTestPart_add_exteriorTestPart (endpointTrim S n) x

end Torsion.Spectral

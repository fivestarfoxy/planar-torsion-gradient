module

public import Torsion.Proof.PaperBoundaryArclength

@[expose] public section

/-! # Detection of the sharp Hermite–Hadamard coefficient by harmonic tests

Uniform approximation of smooth nonnegative boundary data by genuine harmonic
traces transfers the sharp coefficient of the boundary flux measure to volume.
The comparison is quantitative and uses only finite arclength on the boundary. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion.HermiteHadamard

private theorem boundary_pairing_error {K : Set Plane} (hK : IsCompact K) (σ : Measure Plane)
    [IsFiniteMeasureOnCompacts σ] {P f b : Plane → ℝ}
    (hP : ContinuousOn P K) (hf : ContinuousOn f K) (hb : ContinuousOn b K)
    {ε : ℝ} (hclose : ∀ x ∈ K, |f x - b x| ≤ ε) :
    |(∫ x in K, f x * P x ∂σ) - ∫ x in K, b x * P x ∂σ| ≤ ε * ∫ x in K, |P x| ∂σ := by
  have h1 : IntegrableOn (fun x => f x * P x) K σ := (hf.mul hP).integrableOn_compact hK
  have h2 : IntegrableOn (fun x => b x * P x) K σ := (hb.mul hP).integrableOn_compact hK
  rw [← integral_sub h1 h2,
    ← integral_const_mul, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le ((hP.abs.integrableOn_compact hK).const_mul ε)
  filter_upwards [ae_restrict_mem (μ := σ) hK.measurableSet] with x hx
  rw [← sub_mul, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hclose x hx) (abs_nonneg _)

/-- If the volume functional satisfies the weighted boundary identity on a
class of actual harmonic tests whose traces approximate nonnegative smooth
data, then every Hermite–Hadamard coefficient is at least the maximum slope. -/
theorem lower_bound_of_harmonic_approximation {D K : Set Plane} (hK : IsCompact K) (σ : Measure Plane)
    [IsFiniteMeasureOnCompacts σ] {p : Plane} (hp : p ∈ K)
    (hmass : ∀ r > 0, 0 < (σ.restrict K) (Metric.ball p r))
    {q : Plane → ℝ} (hq : ContinuousOn q K) (hmax : ∀ x ∈ K, q x ≤ q p)
    (tests : Set (Plane → ℝ))
    (happrox : ∀ b : Plane → ℝ, ContDiff ℝ ∞ b → HasCompactSupport b → (∀ x, 0 ≤ b x) →
      ∀ ε > 0, ∃ f ∈ tests, ContinuousOn f K ∧ ∀ x ∈ K, |f x - b x| ≤ ε)
    (hgreen : ∀ f ∈ tests, (∫ x in D, f x) = ∫ x in K, f x * q x ∂σ)
    {C : ℝ} (hbound : ∀ f ∈ tests, (∫ x in D, f x) ≤ C * ∫ x in K, f x ∂σ) : q p ≤ C := by
  apply (boundary_coefficient_iff hK σ hp hmass hq hmax C).mp
  intro b hb hbc hb0
  let P := fun x => q x - C
  have hP : ContinuousOn P K := hq.sub continuousOn_const
  have hpair (v : Plane → ℝ) (hv : ContinuousOn v K) :
      (∫ x in K, v x * P x ∂σ) = (∫ x in K, v x * q x ∂σ) - C * ∫ x in K, v x ∂σ := by
    have h1 : IntegrableOn (fun x => v x * q x) K σ := (hv.mul hq).integrableOn_compact hK
    have h2 : IntegrableOn (fun x => v x * C) K σ := (hv.integrableOn_compact hK).mul_const C
    simp only [P, mul_sub, integral_sub h1 h2, integral_mul_const, mul_comm C]
  by_contra! hfalse
  let A := ∫ x in K, b x * P x ∂σ
  have hA : 0 < A := by dsimp only [A]; rw [hpair _ hb.continuous.continuousOn]; linarith
  let M := ∫ x in K, |P x| ∂σ
  have hM : 0 ≤ M := integral_nonneg fun x => abs_nonneg _
  have hden : 0 < M + 1 := by linarith
  let ε := A / (M + 1)
  have hε : 0 < ε := div_pos hA hden
  obtain ⟨f, htest, hc, hclose⟩ := happrox _ hb hbc hb0 ε hε
  have hf : (∫ x in K, f x * P x ∂σ) ≤ 0 := by
    rw [hpair _ hc, ← hgreen _ htest]
    linarith [hbound _ htest]
  have herr := boundary_pairing_error hK σ hP hc hb.continuous.continuousOn hclose
  change |(∫ x in K, f x * P x ∂σ) - A| ≤ ε * M at herr
  have hdiff := (abs_le.mp herr).1
  have heq : ε * (M + 1) = A := div_mul_cancel₀ _ hden.ne'
  nlinarith

end Torsion.HermiteHadamard

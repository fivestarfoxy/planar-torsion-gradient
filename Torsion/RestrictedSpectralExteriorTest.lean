module

public import Torsion.RestrictedSpectralExteriorEnergy
public import Torsion.RestrictedSpectralExteriorKernel
public import Torsion.RestrictedSpectralFourierContinuity
public import Torsion.RestrictedSpectralWeakPrimitive
public import Torsion.RestrictedSpectralSchwartz

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Testing the actual restricted density against exterior smooth data

The exterior datum is separated from the closed interval. Absolute Fubini
then identifies its actual two-point kernel, and the defining original
core approximation extends the smooth interior test identity to every
member of the existing restricted Fourier form domain.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff SchwartzMap

namespace Torsion.Spectral

/-- Actual cross energies are continuous under convergence of the original
energy difference, also when the fixed test has no restricted support. -/
theorem energy_pairing_tendsto_of_difference {f g : ℝ → ℝ} {v : ℕ → ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hv : ∀ n, Integrable (v n))
    (hef : FiniteEnergy f) (heg : FiniteEnergy g) (hev : ∀ n, FiniteEnergy (v n))
    (hE : Tendsto (fun n => energy (fun x => v n x - f x)
      (fun x => v n x - f x)) atTop (𝓝 0)) :
    Tendsto (fun n => energy (v n) g) atTop (𝓝 (energy f g)) := by
  let V : ℕ → Lp ℂ 2 (volume : Measure ℝ) := fun n => halfDerivative (v n) (hv n) (hev n)
  let F := halfDerivative f hf hef
  have heq (n : ℕ) : ‖V n - F‖ ^ 2 =
      (2 * Real.pi) * energy (fun x => v n x - f x) (fun x => v n x - f x) := by
    rw [energy_sub_eq_norm_halfDerivative_sub (hv n) hf (hev n) hef]
    dsimp only [V, F]
    field_simp
  have hsq : Tendsto (fun n => ‖V n - F‖ ^ 2) atTop (𝓝 0) := by
    simpa only [heq, mul_zero] using hE.const_mul (2 * Real.pi)
  have hnorm : Tendsto (fun n => ‖V n - F‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq
  have hV : Tendsto V atTop (𝓝 F) := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have hinner := hV.inner (𝕜 := ℝ) (tendsto_const_nhds (x := halfDerivative g hg heg))
  simpa only [energy_eq_inner_halfDerivative (hv _) hg (hev _) heg,
    energy_eq_inner_halfDerivative hf hg hef heg, V, F] using
    hinner.const_mul (1 / (2 * Real.pi))

private theorem exteriorTest_gap {δ x y : ℝ} (_hδ : 0 < δ)
    (hx : |x| ≤ 1) (hy : ¬ |y| < 1 + δ) : δ ≤ |x - y| := by
  have hy' : 1 + δ ≤ |y| := le_of_not_gt hy
  have h := abs_sub_abs_le_abs_sub y x
  rw [abs_sub_comm y x] at h
  linarith

/-- A strict gap from the source interval bounds every actual double-pole
integral of the exterior datum uniformly on that interval. -/
theorem exteriorTest_kernel_bound {S : ℝ → ℝ} (hS : Integrable S)
    {δ : ℝ} (hδ : 0 < δ) (hz : ∀ y, |y| < 1 + δ → S y = 0)
    {x : ℝ} (hx : |x| ≤ 1) :
    |∫ y : ℝ, S y / (x - y) ^ 2| ≤ (∫ y : ℝ, ‖S y‖) / δ ^ 2 := by
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_div]
  apply integral_mono_of_nonneg
    (ae_of_all _ fun y => norm_nonneg _) (hS.norm.div_const _)
  exact ae_of_all _ fun y => by
    dsimp only
    by_cases hy : |y| < 1 + δ
    · simp [hz y hy, div_nonneg (norm_nonneg _) (sq_nonneg _)]
    · rw [norm_div, norm_pow, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hδ)
        (pow_le_pow_left₀ hδ.le (exteriorTest_gap hδ hx hy) 2)

/-- The separated physical two-point kernel is absolutely integrable for
any actual L¹ source supported on the original interval. -/
theorem integrable_exteriorTest_kernel {f S : ℝ → ℝ}
    (hf : Integrable f) (hS : Integrable S)
    (hfzero : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x = 0)
    {δ : ℝ} (hδ : 0 < δ) (hz : ∀ y, |y| < 1 + δ → S y = 0) :
    Integrable (fun p : ℝ × ℝ => f p.1 * S p.2 / (p.1 - p.2) ^ 2)
      (volume : Measure (ℝ × ℝ)) := by
  have hmajor := (hf.norm.mul_prod hS.norm).div_const (δ ^ 2)
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 * S p.2 / (p.1 - p.2) ^ 2)
      (volume : Measure (ℝ × ℝ)) := by
    simpa only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, Pi.sub_apply, Function.comp_apply] using!
      ((hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume))).mul
        (hS.aestronglyMeasurable.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)))).mul
        ((((measurable_fst.sub measurable_snd).pow_const 2).inv).aestronglyMeasurable)
  apply hmajor.mono' hm
  have hae := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).ae hfzero
  filter_upwards [hae] with p hp
  by_cases hx : p.1 ∈ Ioo (-1 : ℝ) 1
  · by_cases hy : |p.2| < 1 + δ
    · simp [hz p.2 hy]
    · simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (sq_pos_of_pos hδ)
        (pow_le_pow_left₀ hδ.le (exteriorTest_gap hδ (abs_le.2 ⟨hx.1.le, hx.2.le⟩) hy) 2)
  · simp [hp hx]

/-- Absolute Fubini identifies the actual full exterior residual pairing
with the genuine separated-kernel pairing on the source interval. -/
theorem integral_exteriorTest_kernel_eq_residual {f S : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hS : Integrable S)
    {δ : ℝ} (hδ : 0 < δ) (hz : ∀ y, |y| < 1 + δ → S y = 0) :
    (1 / Real.pi) * (∫ x : ℝ, f x * (∫ y : ℝ, S y / (x - y) ^ 2)) =
      ∫ y : ℝ, exteriorResidualZero f y * S y := by
  have hi := integrable_exteriorTest_kernel hf.integrable hS hf.2.2.1 hδ hz
  have hswap := integral_integral_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (f := fun x y : ℝ => f x * S y / (x - y) ^ 2) hi
  have hleft : (∫ x : ℝ, ∫ y : ℝ, f x * S y / (x - y) ^ 2) =
      ∫ x : ℝ, f x * (∫ y : ℝ, S y / (x - y) ^ 2) := by
    congr 1
    funext x
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  have hright : (∫ y : ℝ, ∫ x : ℝ, f x * S y / (x - y) ^ 2) =
      ∫ y : ℝ, S y * (∫ x : ℝ, f x / (y - x) ^ 2) := by
    congr 1
    funext y
    rw [← integral_const_mul]
    congr 1
    funext x
    have hd : (x - y) ^ 2 = (y - x) ^ 2 := by ring
    rw [hd]
    ring
  rw [hleft, hright] at hswap
  rw [hswap, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    by_cases hy : 1 < |y|
    · change (1 / Real.pi) * (S y * (∫ x : ℝ, f x / (y - x) ^ 2)) =
        exteriorResidualZero f y * S y
      simp only [exteriorResidualZero, if_pos hy, hf.exteriorResidual_eq_whole y]
      ring
    · have hyS : S y = 0 := hz y (by linarith [le_of_not_gt hy])
      simp [hyS]


/-- The actual source pairing with a uniformly separated exterior kernel is
integrable, without any pointwise regularity of the source density. -/
theorem integrable_source_mul_exteriorTest_kernel {f S : ℝ → ℝ}
    (hf : Integrable f) (hS : Integrable S)
    (hfzero : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x = 0)
    {δ : ℝ} (hδ : 0 < δ) (hz : ∀ y, |y| < 1 + δ → S y = 0) :
    Integrable (fun x : ℝ => f x * (∫ y : ℝ, S y / (x - y) ^ 2)) := by
  have hi := integrable_exteriorTest_kernel hf hS hfzero hδ hz
  convert hi.integral_prod_left using 1
  funext x
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

/-- Strong L¹ convergence of actual interval-supported densities passes
through the uniformly separated exterior double-pole pairing. -/
theorem integral_source_mul_exteriorTest_kernel_tendsto
    {f S : ℝ → ℝ} {v : ℕ → ℝ → ℝ}
    (hf : Integrable f) (hS : Integrable S) (hv : ∀ n, Integrable (v n))
    (hfzero : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x = 0)
    (hvzero : ∀ n, ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0)
    {δ : ℝ} (hδ : 0 < δ) (hz : ∀ y, |y| < 1 + δ → S y = 0)
    (hL : Tendsto (fun n => ∫ x : ℝ, ‖v n x - f x‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : ℝ, v n x * (∫ y : ℝ, S y / (x - y) ^ 2))
      atTop (𝓝 (∫ x : ℝ, f x * (∫ y : ℝ, S y / (x - y) ^ 2))) := by
  let K : ℝ → ℝ := fun x => ∫ y : ℝ, S y / (x - y) ^ 2
  let C : ℝ := (∫ y : ℝ, ‖S y‖) / δ ^ 2
  have hC : 0 ≤ C := div_nonneg (integral_nonneg fun y => norm_nonneg _) (sq_nonneg _)
  have hfi : Integrable (fun x => f x * K x) :=
    integrable_source_mul_exteriorTest_kernel hf hS hfzero hδ hz
  have hvi (n : ℕ) : Integrable (fun x => v n x * K x) :=
    integrable_source_mul_exteriorTest_kernel (hv n) hS (hvzero n) hδ hz
  have heq (n : ℕ) : (∫ x : ℝ, v n x * K x) - (∫ x : ℝ, f x * K x) =
      ∫ x : ℝ, (v n x - f x) * K x := by
    rw [← integral_sub (hvi n) hfi]
    congr 1
    funext x
    ring
  have hbound (n : ℕ) : |∫ x : ℝ, (v n x - f x) * K x| ≤
      C * (∫ x : ℝ, ‖v n x - f x‖) := by
    rw [← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _)
      (((hv n).sub hf).norm.const_mul C)
    filter_upwards [hfzero, hvzero n] with x hx hvx
    by_cases hxi : x ∈ Ioo (-1 : ℝ) 1
    · have hK := exteriorTest_kernel_bound hS hδ hz (abs_le.2 ⟨hxi.1.le, hxi.2.le⟩)
      rw [norm_mul]
      change ‖v n x - f x‖ * |K x| ≤ C * ‖v n x - f x‖
      exact (mul_le_mul_of_nonneg_left hK (norm_nonneg _)).trans_eq (mul_comm _ _)
    · simp [hx hxi, hvx hxi]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hup : Tendsto (fun n => C * (∫ x : ℝ, ‖v n x - f x‖)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hL.const_mul C
  apply squeeze_zero (fun _ => norm_nonneg _) _ hup
  intro n
  change ‖(∫ x : ℝ, v n x * K x) - (∫ x : ℝ, f x * K x)‖ ≤ _
  rw [heq, Real.norm_eq_abs]
  exact hbound n

/-- The actual weak Fourier form against an exterior Schwartz test equals
the negative pairing with the concrete exterior residual. The strict gap
is the only condition on the test's support. -/
theorem MemRestrictedFormDomain.energy_schwartz_exterior {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (S : 𝓢(ℝ, ℝ))
    (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x| < 1 + δ → S x = 0) :
    energy f S = -(∫ x : ℝ, exteriorResidualZero f x * S x) := by
  obtain ⟨δ, hδ, hz⟩ := hgap
  obtain ⟨v, hv, hL2, hE⟩ := hf.2.2.2
  have hvI (n : ℕ) : Integrable (v n) := (hv n).memRestrictedFormDomain.integrable
  have hvE (n : ℕ) : FiniteEnergy (v n) := (hv n).memRestrictedFormDomain.2.1
  have hvzero (n : ℕ) : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0 :=
    (hv n).memRestrictedFormDomain.2.2.1
  have hL1 := tendsto_eLpNorm_one_of_two_zero_exterior
    (fun n => (hv n).memRestrictedFormDomain.1) hf.1 hvzero hf.2.2.1 hL2
  have hL := integral_norm_sub_tendsto_of_eLpNorm_one hvI hf.integrable hL1
  have hleft := energy_pairing_tendsto_of_difference hf.integrable S.integrable hvI
    hf.2.1 (finiteEnergy_of_schwartz S) hvE hE
  have hright := (integral_source_mul_exteriorTest_kernel_tendsto hf.integrable
    S.integrable hvI hf.2.2.1 hvzero hδ hz hL).const_mul (-(1 / Real.pi))
  have hSzero : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → S x = 0 :=
    ae_of_all _ fun x hx => hz x (by have ha := abs_lt.2 hx; linarith)
  have heq (n : ℕ) : energy (v n) S =
      -(1 / Real.pi) * (∫ x : ℝ, v n x * (∫ y : ℝ, S y / (x - y) ^ 2)) := by
    rw [energy_symm]
    exact energy_eq_exterior_kernel_pairing S.integrable hSzero (hv n)
  have hleft' : Tendsto (fun n => -(1 / Real.pi) *
      (∫ x : ℝ, v n x * (∫ y : ℝ, S y / (x - y) ^ 2))) atTop (𝓝 (energy f S)) := by
    simpa only [heq] using hleft
  have hlimit := tendsto_nhds_unique hleft' hright
  have hres := integral_exteriorTest_kernel_eq_residual hf S.integrable hδ hz
  calc
    energy f S = -((1 / Real.pi) *
        (∫ x : ℝ, f x * (∫ y : ℝ, S y / (x - y) ^ 2))) := by linarith
    _ = _ := by rw [hres]

end Torsion.Spectral

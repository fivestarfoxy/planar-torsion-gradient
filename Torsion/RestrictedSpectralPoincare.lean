module

public import Torsion.FourierPlancherel
public import Torsion.FourierHilbertPairing
public import Torsion.RestrictedSpectralEnergyContinuity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Coercivity of the concrete restricted Fourier form

A frequency split at `π/4`, combined with the actual support interval and
Parseval, gives a positive Poincaré constant for the restricted form.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform SchwartzMap

namespace Torsion.Spectral

/-- The actual support interval of length two gives the precise elementary
L¹–L² estimate, proved by integrating an ordinary nonnegative square. -/
theorem IsCore.integral_norm_sq_le {f : ℝ → ℝ} (hf : IsCore f) :
    (∫ x : ℝ, ‖f x‖) ^ 2 ≤ 2 * ∫ x : ℝ, f x ^ 2 := by
  let A : ℝ := ∫ x in Icc (-1 : ℝ) 1, ‖f x‖
  have hzero (x : ℝ) (hx : x ∉ Icc (-1 : ℝ) 1) : f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (Ioo_subset_Icc_self (hf.2.2 h)))
  have hA : (∫ x : ℝ, ‖f x‖) = A := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzero x hx]; simp)
  have hS : (∫ x : ℝ, f x ^ 2) = ∫ x in Icc (-1 : ℝ) 1, f x ^ 2 := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzero x hx]; simp)
  have hfi : IntegrableOn (fun x => f x ^ 2) (Icc (-1 : ℝ) 1) :=
    (hf.1.continuous.pow 2).integrableOn_Icc
  have hfn : IntegrableOn (fun x => ‖f x‖) (Icc (-1 : ℝ) 1) :=
    hf.1.continuous.norm.integrableOn_Icc
  have hsub : IntegrableOn (fun x => f x ^ 2 - A * ‖f x‖) (Icc (-1 : ℝ) 1) :=
    hfi.sub (hfn.const_mul A)
  have hconst : IntegrableOn (fun _ : ℝ => A ^ 2 / 4) (Icc (-1 : ℝ) 1) :=
    continuous_const.integrableOn_Icc
  have hnonneg : 0 ≤ ∫ x in Icc (-1 : ℝ) 1, (‖f x‖ - A / 2) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hex : (∫ x in Icc (-1 : ℝ) 1, (‖f x‖ - A / 2) ^ 2) =
      (∫ x in Icc (-1 : ℝ) 1, f x ^ 2) - A * A + 2 * (A ^ 2 / 4) := by
    calc
      _ = ∫ x in Icc (-1 : ℝ) 1, (f x ^ 2 - A * ‖f x‖) + A ^ 2 / 4 := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          dsimp only
          rw [Real.norm_eq_abs]
          nlinarith [sq_abs (f x)]
      _ = _ := by
        rw [integral_add hsub hconst,
          integral_sub hfi (hfn.const_mul A), integral_const_mul,
          setIntegral_const, Real.volume_real_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        simp only [smul_eq_mul]
        norm_num [A]
  rw [hA, hS]
  rw [hex] at hnonneg
  nlinarith

/-- Pointwise Fourier bound with the support's exact length. -/
theorem IsCore.norm_fourier_sq_le {f : ℝ → ℝ} (hf : IsCore f) (ξ : ℝ) :
    ‖fourier f ξ‖ ^ 2 ≤ 2 * ∫ x : ℝ, f x ^ 2 := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_fourier_le_integral_norm f ξ) 2).trans
    hf.integral_norm_sq_le

/-- A concrete fractional Poincaré bound on the original smooth restricted
core. The frequency split absorbs half the actual L² mass. -/
theorem IsCore.fractional_poincare {f : ℝ → ℝ} (hf : IsCore f) :
    (∫ x : ℝ, f x ^ 2) ≤ (8 / Real.pi) * energy f f := by
  let S : ℝ := ∫ x : ℝ, f x ^ 2
  let δ : ℝ := Real.pi / 4
  let W : ℝ → ℝ := fun ξ => |ξ| * ‖fourier f ξ‖ ^ 2
  let B : ℝ → ℝ := fun ξ =>
    (Icc (-δ) δ).indicator (fun _ : ℝ => 2 * S) ξ + (4 / Real.pi) * W ξ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have he : Integrable W := finiteEnergy_of_contDiff_hasCompactSupport hf.1 hf.2.1
  have hi : Integrable (fun ξ : ℝ => ‖fourier f ξ‖ ^ 2) :=
    integrable_norm_sq_fourier_of_core hf.1 hf.2.1
  have hbi : Integrable ((Icc (-δ) δ).indicator (fun _ : ℝ => 2 * S)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc
  have hb : Integrable B := hbi.add (he.const_mul (4 / Real.pi))
  have hpoint (ξ : ℝ) : ‖fourier f ξ‖ ^ 2 ≤ B ξ := by
    by_cases hξ : ξ ∈ Icc (-δ) δ
    · simp only [B, indicator_of_mem hξ]
      exact (hf.norm_fourier_sq_le ξ).trans (le_add_of_nonneg_right (by
        dsimp [W]
        positivity))
    · have hξabs : δ ≤ |ξ| := by
        by_contra h
        have hlt : |ξ| < δ := lt_of_not_ge h
        exact hξ (abs_le.mp hlt.le)
      have hfactor : 1 ≤ (4 / Real.pi) * |ξ| := by
        have hh : Real.pi ≤ 4 * |ξ| := by dsimp [δ] at hξabs; linarith
        have h : 1 ≤ (4 * |ξ|) / Real.pi :=
          (le_div_iff₀ Real.pi_pos).mpr (by simpa using hh)
        simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
      simp only [B, indicator_of_notMem hξ, zero_add, W]
      calc
        ‖fourier f ξ‖ ^ 2 = 1 * ‖fourier f ξ‖ ^ 2 := by ring
        _ ≤ ((4 / Real.pi) * |ξ|) * ‖fourier f ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)
        _ = _ := by ring
  have hE : (∫ ξ : ℝ, W ξ) = (2 * Real.pi) * energy f f := by
    rw [energy_self]
    dsimp only [W]
    field_simp [Real.pi_ne_zero]
  have hB : (∫ ξ : ℝ, B ξ) = Real.pi * S + 8 * energy f f := by
    dsimp only [B]
    rw [integral_add hbi (he.const_mul (4 / Real.pi)), integral_indicator measurableSet_Icc,
      setIntegral_const, Real.volume_real_Icc_of_le (by linarith : -δ ≤ δ),
      integral_const_mul, hE]
    simp only [smul_eq_mul]
    dsimp only [δ]
    field_simp [Real.pi_ne_zero]
    ring
  have hfull : (2 * Real.pi) * S ≤ Real.pi * S + 8 * energy f f := by
    simpa only [integral_norm_sq_fourier_of_core hf.1 hf.2.1, hB] using
      integral_mono hi hb hpoint
  have hco : Real.pi * S ≤ 8 * energy f f := by linarith
  have hco' : S ≤ (8 * energy f f) / Real.pi :=
    (le_div_iff₀ Real.pi_pos).mpr (by nlinarith [hco])
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hco'

/-- The same genuine coercivity bound holds in the actual restricted
form domain, by its defining L² and half-energy approximation. -/
theorem MemRestrictedFormDomain.fractional_poincare {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) :
    (∫ x : ℝ, f x ^ 2) ≤ (8 / Real.pi) * energy f f := by
  obtain ⟨v, hv, hL, hE⟩ := hf.2.2.2
  have hvL (n : ℕ) : MemLp (v n) 2 volume :=
    (hv n).1.continuous.memLp_of_hasCompactSupport (hv n).2.1
  have hvI (n : ℕ) : Integrable (v n) :=
    (hv n).1.continuous.integrable_of_hasCompactSupport (hv n).2.1
  have hvE (n : ℕ) : FiniteEnergy (v n) :=
    finiteEnergy_of_contDiff_hasCompactSupport (hv n).1 (hv n).2.1
  have hSq := integral_sq_tendsto_of_eLpNorm_sub hf.1 hvL hL
  have hEn := energy_tendsto_of_difference hf.integrable hvI hf.2.1 hvE hE
  exact le_of_tendsto_of_tendsto hSq (hEn.const_mul (8 / Real.pi))
    (Eventually.of_forall fun n => (hv n).fractional_poincare)

/-- Positive coercivity of the original Fourier integral, with an explicit
constant and the actual Lebesgue L² mass. -/
theorem MemRestrictedFormDomain.energy_ge {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) :
    (Real.pi / 8) * (∫ x : ℝ, f x ^ 2) ≤ energy f f := by
  have h := hf.fractional_poincare
  have hmul := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ Real.pi / 8 by positivity)
  have hfac : (Real.pi / 8) * (8 / Real.pi) = 1 := by field_simp [Real.pi_ne_zero]
  simpa only [← mul_assoc, hfac, one_mul] using hmul

/-- Every actual restricted weak eigenvalue has a quantitative positive
lower bound supplied by the concrete form's coercivity. -/
theorem IsRestrictedEigenfunction.eigenvalue_ge_pi_div_eight
    {a : ℝ} {φ : ℝ → ℝ} (hφ : IsRestrictedEigenfunction a φ) :
    Real.pi / 8 ≤ a := by
  have hs : 0 < ∫ x : ℝ, φ x ^ 2 := by
    simpa only [pow_two] using hφ.square_integral_pos
  have h := hφ.1.energy_ge
  rw [hφ.2.2 φ hφ.1] at h
  have hsq : (∫ x : ℝ, φ x * φ x) = ∫ x : ℝ, φ x ^ 2 := by
    congr 1
    funext x
    ring
  rw [hsq] at h
  exact (mul_le_mul_right hs).mp h

end Torsion.Spectral

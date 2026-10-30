import Torsion.CauchyTransformImaginaryBoundary
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder calculus for the actual integrated spectral densities

The integrated profile and the product `Yφ` inherit a positive Hölder
exponent from `φ`.  The proof first obtains a genuine global Lipschitz bound
for `Y` from its proved derivative, and then uses boundedness of the actual
compactly supported functions.  Thus regularity of the auxiliary derivative
density need not be an additional spectral assumption.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- Real distance inequalities give the ENNReal formulation of Hölder
continuity used by mathlib. -/
theorem holderWith_of_dist_bound {C α : ℝ≥0} {f : ℝ → ℝ}
    (h : ∀ x y : ℝ, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (α : ℝ)) :
    HolderWith C α f := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist x y)
    α.coe_nonneg, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x y)

/-- A bounded globally Lipschitz real function is Hölder for every exponent
at most one, with an explicit finite constant. -/
theorem holderWith_of_bounded_lipschitz {f : ℝ → ℝ} {K B α : ℝ≥0}
    (hLip : LipschitzWith K f) (hB : ∀ x : ℝ, ‖f x‖ ≤ (B : ℝ))
    (hα : α ≤ 1) : HolderWith (max K (2 * B)) α f := by
  apply holderWith_of_dist_bound
  intro x y
  have hd0 : 0 ≤ dist x y := dist_nonneg
  have hp0 : 0 ≤ dist x y ^ (α : ℝ) := Real.rpow_nonneg hd0 _
  simp only [NNReal.coe_max, NNReal.coe_mul, NNReal.coe_ofNat]
  by_cases hd : dist x y ≤ 1
  · have hpow : dist x y ≤ dist x y ^ (α : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' hd0 hd α.coe_nonneg
        (show (α : ℝ) ≤ 1 by exact_mod_cast hα)
    exact (hLip.dist_le_mul x y).trans
      ((mul_le_mul_of_nonneg_left hpow K.coe_nonneg).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hp0))
  · have hp : 1 ≤ dist x y ^ (α : ℝ) :=
      Real.one_le_rpow (le_of_not_ge hd) α.coe_nonneg
    have hf : dist (f x) (f y) ≤ 2 * (B : ℝ) := by
      calc
        dist (f x) (f y) = ‖f x - f y‖ := dist_eq_norm _ _
        _ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
        _ ≤ 2 * (B : ℝ) := by linarith [hB x, hB y]
    exact hf.trans ((le_mul_of_one_le_right (by positivity) hp).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hp0))

/-- Multiplication preserves a common Hölder exponent when both actual
functions are bounded. -/
theorem holderWith_mul_of_bounded {f g : ℝ → ℝ} {C D Bf Bg α : ℝ≥0}
    (hf : HolderWith C α f) (hg : HolderWith D α g)
    (hBf : ∀ x : ℝ, ‖f x‖ ≤ (Bf : ℝ)) (hBg : ∀ x : ℝ, ‖g x‖ ≤ (Bg : ℝ)) :
    HolderWith (Bf * D + Bg * C) α (fun x => f x * g x) := by
  apply holderWith_of_dist_bound
  intro x y
  have hsplit : f x * g x - f y * g y =
      f x * (g x - g y) + g y * (f x - f y) := by ring
  calc
    dist (f x * g x) (f y * g y) =
        ‖f x * (g x - g y) + g y * (f x - f y)‖ := by rw [dist_eq_norm, hsplit]
    _ ≤ ‖f x‖ * dist (g x) (g y) + ‖g y‖ * dist (f x) (f y) := by
      simpa only [norm_mul, dist_eq_norm] using
        norm_add_le (f x * (g x - g y)) (g y * (f x - f y))
    _ ≤ (Bf : ℝ) * ((D : ℝ) * dist x y ^ (α : ℝ)) +
        (Bg : ℝ) * ((C : ℝ) * dist x y ^ (α : ℝ)) :=
      add_le_add (mul_le_mul (hBf x) (hg.dist_le x y) dist_nonneg Bf.coe_nonneg)
        (mul_le_mul (hBg y) (hf.dist_le x y) dist_nonneg Bg.coe_nonneg)
    _ = ((Bf * D + Bg * C : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
      push_cast
      ring

/-- Compactness supplies an actual finite nonnegative bound on the
continuous densities used in the spectral construction. -/
theorem exists_nnreal_bound_of_compactSupport {f : ℝ → ℝ}
    (hf : Continuous f) (hsupp : HasCompactSupport f) :
    ∃ B : ℝ≥0, ∀ x : ℝ, ‖f x‖ ≤ (B : ℝ) := by
  obtain ⟨B, hB⟩ := hsupp.exists_bound_of_continuous hf
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hB 0)
  lift B to ℝ≥0 using hB0
  exact ⟨B, hB⟩

/-- The actual integrated profile is globally Lipschitz, without assuming
any derivative bound separately. -/
theorem height_exists_lipschitz {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    ∃ K : ℝ≥0, LipschitzWith K (height φ) := by
  obtain ⟨K, hK⟩ := exists_nnreal_bound_of_compactSupport hφ
    (cauchyDensity_hasCompactSupport hzero)
  refine ⟨K, lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_height hφ hodd hzero x).differentiableAt) ?_⟩
  intro x
  rw [deriv_height_eq hφ hodd hzero x, nnnorm_neg]
  exact_mod_cast hK x

/-- For every exponent at most one, the height inherits a global Hölder
estimate from the genuine Lipschitz and compact-support bounds. -/
theorem height_exists_holder {φ : ℝ → ℝ} {α : ℝ≥0}
    (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderWith C α (height φ) := by
  obtain ⟨K, hK⟩ := height_exists_lipschitz hφ hodd hzero
  obtain ⟨B, hB⟩ := exists_nnreal_bound_of_compactSupport
    (height_continuous hφ.continuousOn) (height_hasCompactSupport φ)
  exact ⟨max K (2 * B), holderWith_of_bounded_lipschitz hK hB hα⟩

/-- A globally Hölder odd zero-exterior eigenfunction gives a genuine
Hölder estimate for the auxiliary derivative density `Yφ`. -/
theorem height_mul_exists_holder {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    ∃ D : ℝ≥0, HolderWith D α (fun x => height φ x * φ x) := by
  have hcont := hφ.continuous hα0
  obtain ⟨CY, hY⟩ := height_exists_holder hcont hodd hzero hα1
  obtain ⟨BY, hBY⟩ := exists_nnreal_bound_of_compactSupport
    (height_continuous hcont.continuousOn) (height_hasCompactSupport φ)
  obtain ⟨Bφ, hBφ⟩ := exists_nnreal_bound_of_compactSupport hcont
    (cauchyDensity_hasCompactSupport hzero)
  exact ⟨BY * C + Bφ * CY, holderWith_mul_of_bounded hY hφ hBY hBφ⟩

end Torsion.Spectral

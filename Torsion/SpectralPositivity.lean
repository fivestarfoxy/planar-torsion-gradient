import Torsion.SpectralDefinitions
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Positivity of the integrated spectral profile

These are concrete consequences of continuity and strict positivity of `φ`
on `(0,1)`. They do not assume any eigenfunction equation or moment identity.
Establishing those hypotheses for the second restricted half-Laplacian
eigenfunction remains a separate spectral obligation.
-/

noncomputable section
open Set MeasureTheory

namespace Torsion.Spectral

/-- The zero-extended height profile is even directly from its definition. -/
theorem height_even (φ : ℝ → ℝ) : Function.Even (height φ) := by
  intro x
  simp [height, abs_neg]

/-- The prescribed exterior values include both endpoints. -/
theorem height_zero_of_one_le_abs (φ : ℝ → ℝ) {x : ℝ} (hx : 1 ≤ |x|) :
    height φ x = 0 := by
  simp [height, not_lt.mpr hx]

/-- Nonnegative data on `[0,1]` give a globally nonnegative height profile. -/
theorem height_nonneg {φ : ℝ → ℝ}
    (hφ : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ φ s) (x : ℝ) :
    0 ≤ height φ x := by
  unfold height
  split_ifs with hx
  · apply setIntegral_nonneg measurableSet_Icc
    intro s hs
    exact hφ s ⟨(abs_nonneg x).trans hs.1, hs.2⟩
  · exact le_rfl

/-- An interval-integral description valid both inside and outside the
support. Clamping the lower endpoint makes continuity transparent. -/
theorem height_eq_clamped_integral (φ : ℝ → ℝ) (x : ℝ) :
    height φ x = ∫ s in (min |x| 1)..1, φ s := by
  by_cases hx : |x| < 1
  · rw [height, if_pos hx, min_eq_left hx.le,
      intervalIntegral.integral_of_le hx.le, integral_Icc_eq_integral_Ioc]
  · have hle : 1 ≤ |x| := le_of_not_gt hx
    simp [height, hx, min_eq_right hle]

/-- Continuity on the closed positive half-interval is enough for global
continuity of the integrated, zero-extended height profile. -/
theorem height_continuous {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    Continuous (height φ) := by
  have hint : IntegrableOn φ (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hφ.integrableOn_Icc
  have hp : ContinuousOn (fun x : ℝ => ∫ s in x..1, φ s) (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      intervalIntegral.continuousOn_primitive_interval_left hint
  have hc := hp.comp_continuous (continuous_abs.min continuous_const)
    (fun x : ℝ => show min |x| 1 ∈ Icc (0 : ℝ) 1 from
      ⟨le_min (abs_nonneg x) (by norm_num), min_le_right _ _⟩)
  convert hc using 1
  funext x
  exact height_eq_clamped_integral φ x

theorem height_integrableOn {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    IntegrableOn (height φ) (Icc (-1 : ℝ) 1) :=
  (height_continuous hcont).integrableOn_Icc

theorem squareHeight_integrableOn {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    IntegrableOn (fun x => (height φ x) ^ 2) (Icc (-1 : ℝ) 1) :=
  ((height_continuous hcont).pow 2).integrableOn_Icc

/-- Strict positivity on `(0,1)` makes the height positive on `(-1,1)`. -/
theorem height_pos {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s)
    {x : ℝ} (hx : |x| < 1) :
    0 < height φ x := by
  rw [height, if_pos hx, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hx.le]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((hcont.mono fun s hs => ⟨(abs_nonneg x).trans hs.1, hs.2⟩).intervalIntegrable_of_Icc hx.le)
    (fun s hs => hpos s ⟨lt_of_le_of_lt (abs_nonneg x) hs.1, hs.2⟩) hx

/-- Strictly positive input has precisely the expected open support. -/
theorem height_support {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    Function.support (height φ) = Ioo (-1 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    have hne : height φ x ≠ 0 := hx
    have habs : |x| < 1 := by
      by_contra hh
      exact hne (height_zero_of_one_le_abs φ (le_of_not_gt hh))
    exact abs_lt.1 habs
  · intro hx
    exact (height_pos hcont hpos (abs_lt.2 hx)).ne'

/-- The mass in (1.3) is strictly positive without using a spectral or
holomorphic identity. -/
theorem mass_pos {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    0 < mass φ := by
  rw [mass, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((height_continuous hcont).intervalIntegrable (-1) 1)
    (fun x hx => height_pos hcont hpos (abs_lt.2 hx)) (by norm_num)

/-- The square mass in (1.3) is likewise strictly positive. -/
theorem squareMass_pos {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s) :
    0 < squareMass φ := by
  rw [squareMass, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (((height_continuous hcont).pow 2).intervalIntegrable (-1) 1)
    (fun x hx => sq_pos_of_pos (height_pos hcont hpos (abs_lt.2 hx))) (by norm_num)

end Torsion.Spectral

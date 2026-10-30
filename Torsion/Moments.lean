module

public import Mathlib.Data.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Exact moment algebra for the spectral construction

This module proves the scalar consequences of (5.4), (7.2), and (7.6) of the
writeup.  `Moments` explicitly assumes positivity and the identity `a * N =
2 * b * M`.  It does not assert that a restricted-half-Laplacian eigenfunction
or its Cauchy transform supplies these data; those are separate analytic
obligations.
-/

namespace Torsion

/-- Positive moment data, conditional on the analytic moment identity (5.4). -/
structure Moments where
  a : ℝ
  b : ℝ
  M : ℝ
  N : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  M_pos : 0 < M
  N_pos : 0 < N
  moment : a * N = 2 * b * M

namespace Moments

noncomputable section

variable (d : Moments)

/-- Area of the constructed reference domain, after its geometric identification. -/
def area : ℝ := d.b * d.M

/-- Marked torsion flux, after the torsion formula has been established. -/
def flux : ℝ := d.b / d.a

/-- The constant value of the product of the two free-boundary normal derivatives. -/
def stationarity : ℝ := 1 / (2 * d.a * d.M)

/-- Candidate sharp constant in Theorem 1.1. -/
noncomputable def sharpConstant : ℝ := Real.sqrt (d.N / (2 * d.a * d.M ^ 2))

@[simp] theorem area_pos : 0 < d.area := mul_pos d.b_pos d.M_pos

@[simp] theorem flux_pos : 0 < d.flux := div_pos d.b_pos d.a_pos

@[simp] theorem stationarity_pos : 0 < d.stationarity := by
  unfold stationarity
  have := d.a_pos
  have := d.M_pos
  positivity

@[simp] theorem sharpConstant_pos : 0 < d.sharpConstant := by
  unfold sharpConstant
  apply Real.sqrt_pos.2
  have := d.a_pos
  have := d.M_pos
  have := d.N_pos
  positivity

/-- First identity in (7.2). -/
theorem area_eq : d.area = d.a * d.N / 2 := by
  unfold area
  nlinarith [d.moment]

/-- Second identity in (7.2). -/
theorem flux_eq : d.flux = d.N / (2 * d.M) := by
  unfold flux
  have := d.M_pos
  apply (div_eq_div_iff (ne_of_gt d.a_pos) (by positivity : 2 * d.M ≠ 0)).2
  nlinarith [d.moment]

/-- Euler identity verified from the exact spectral moments, as in (7.7). -/
theorem euler : d.flux = 2 * d.stationarity * d.area := by
  unfold flux stationarity area
  field_simp [ne_of_gt d.a_pos, ne_of_gt d.M_pos]

/-- The exact square of the normalized flux in the proof of Theorem 1.1. -/
theorem normalized_flux_sq : d.flux ^ 2 / d.area =
    d.N / (2 * d.a * d.M ^ 2) := by
  have hN : d.N = 2 * d.b * d.M / d.a := by
    apply (eq_div_iff (ne_of_gt d.a_pos)).2
    nlinarith [d.moment]
  rw [hN]
  unfold flux area
  field_simp [ne_of_gt d.a_pos, ne_of_gt d.b_pos, ne_of_gt d.M_pos]

/-- The area-normalized flux equals the candidate sharp constant. -/
theorem normalized_flux_eq : d.flux / Real.sqrt d.area = d.sharpConstant := by
  have hs : 0 < Real.sqrt d.area := Real.sqrt_pos.2 d.area_pos
  have hq : 0 < d.flux / Real.sqrt d.area := div_pos d.flux_pos hs
  have he : (d.flux / Real.sqrt d.area) ^ 2 =
      d.N / (2 * d.a * d.M ^ 2) := by
    rw [div_pow, Real.sq_sqrt (le_of_lt d.area_pos)]
    exact d.normalized_flux_sq
  unfold sharpConstant
  rw [← he, Real.sqrt_sq (le_of_lt hq)]

/-- The universal calibration coefficient equals the exact candidate constant. -/
theorem calibration_constant_eq :
    2 * d.stationarity * Real.sqrt d.area = d.sharpConstant := by
  have hs : 0 < Real.sqrt d.area := Real.sqrt_pos.2 d.area_pos
  have hE : d.area / Real.sqrt d.area = Real.sqrt d.area := by
    apply (div_eq_iff (ne_of_gt hs)).2
    nlinarith [Real.sq_sqrt (le_of_lt d.area_pos)]
  calc
    2 * d.stationarity * Real.sqrt d.area =
        2 * d.stationarity * (d.area / Real.sqrt d.area) := by rw [hE]
    _ = d.flux / Real.sqrt d.area := by rw [d.euler]; ring
    _ = d.sharpConstant := d.normalized_flux_eq

/-- Changing the positive normalization of the eigenfunction. -/
def rescale (t : ℝ) (ht : 0 < t) : Moments where
  a := d.a
  b := t * d.b
  M := t * d.M
  N := t ^ 2 * d.N
  a_pos := d.a_pos
  b_pos := mul_pos ht d.b_pos
  M_pos := mul_pos ht d.M_pos
  N_pos := mul_pos (sq_pos_of_pos ht) d.N_pos
  moment := by
    calc
      d.a * (t ^ 2 * d.N) = t ^ 2 * (d.a * d.N) := by ring
      _ = t ^ 2 * (2 * d.b * d.M) := by rw [d.moment]
      _ = 2 * (t * d.b) * (t * d.M) := by ring

/-- Area has degree two under eigenfunction normalization. -/
theorem rescale_area (t : ℝ) (ht : 0 < t) :
    (d.rescale t ht).area = t ^ 2 * d.area := by
  simp only [rescale, area]
  ring

/-- The marked flux has degree one under eigenfunction normalization. -/
theorem rescale_flux (t : ℝ) (ht : 0 < t) :
    (d.rescale t ht).flux = t * d.flux := by
  simp only [rescale, flux]
  ring

/-- The square of the sharp constant is invariant under normalization. -/
theorem rescale_sharpConstant (t : ℝ) (ht : 0 < t) :
    (d.rescale t ht).sharpConstant = d.sharpConstant := by
  unfold sharpConstant
  congr 1
  simp only [rescale]
  field_simp [ne_of_gt ht, ne_of_gt d.a_pos, ne_of_gt d.M_pos]

/-- The scale used to normalize the area compensates for eigenfunction normalization. -/
theorem rescale_normalizing_factor (t : ℝ) (ht : 0 < t) :
    (Real.sqrt (d.rescale t ht).area)⁻¹ * t = (Real.sqrt d.area)⁻¹ := by
  rw [d.rescale_area, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq (le_of_lt ht)]
  field_simp [ne_of_gt ht, ne_of_gt (Real.sqrt_pos.2 d.area_pos)]

end

end Moments
end Torsion

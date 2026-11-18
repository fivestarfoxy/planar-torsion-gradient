module

public import Torsion.Proof.PaperGalerkinTrace
public import Torsion.CauchyTransformHeightDerivative

@[expose] public section

/-! # The height and moments of a finite Galerkin trial profile -/

noncomputable section
open Real Set MeasureTheory
namespace Torsion.Galerkin
open Spectral

/-- The coefficient at index `r` is the amplitude at frequency 2r. -/
def finiteOddProfile (K : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range K, a (r+1) * sin ((2*(r:ℝ)+2)*arccos x)

private theorem profile_continuous (K : ℕ) (a : ℕ → ℝ) : Continuous (finiteOddProfile K a) := by
  unfold finiteOddProfile
  fun_prop

private theorem profile_odd (K : ℕ) (a : ℕ → ℝ) : Function.Odd (finiteOddProfile K a) := by
  intro x
  simp only [finiteOddProfile, arccos_neg, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_sub, show (2*(r:ℝ)+2)*π = ((r+1 : ℕ) : ℝ)*(2*π) by push_cast; ring,
    sin_nat_mul_two_pi_sub, mul_neg]

private theorem profile_zero (K : ℕ) (a : ℕ → ℝ) (x : ℝ) (hx : 1 ≤ |x|) :
    finiteOddProfile K a x = 0 := by
  rcases le_abs.mp hx with h | h
  · simp [finiteOddProfile, arccos_of_one_le h]
  · unfold finiteOddProfile
    rw [arccos_of_le_neg_one (by linarith)]
    apply Finset.sum_eq_zero
    intro r hr
    rw [show 2*(r:ℝ)+2 = ((2*r+2 : ℕ) : ℝ) by push_cast; ring, Real.sin_nat_mul_pi, mul_zero]

/-- The trigonometric trial polynomial is the actual zero-exterior linear
combination of the form-domain basis used in the Ritz matrices. -/
theorem finiteOddProfile_eq_modes (K : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    finiteOddProfile K a x = ∑ r ∈ Finset.range K, a (r+1) * trialMode (2*r+2) x := by
  by_cases hx : |x| ≤ 1
  · unfold finiteOddProfile
    apply Finset.sum_congr rfl
    intro r hr
    rw [trialMode_sine _ hx]
    push_cast
    rfl
  · rw [profile_zero _ _ _ (le_of_not_ge hx)]
    simp [trialMode_zero_exterior _ _ (le_of_not_ge hx)]

private theorem profile_cos (K : ℕ) (a : ℕ → ℝ) {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    finiteOddProfile K a (cos θ) = ∑ r ∈ Finset.range K, a (r+1)*sin ((2*(r:ℝ)+2)*θ) := by
  simp [finiteOddProfile, arccos_cos hθ.1 hθ.2]

/-- The adjacent-frequency coefficients give the actual zero-exterior
spectral height on every cosine ray. -/
theorem finiteOddProfile_height_cos (K : ℕ) (a : ℕ → ℝ) (ha : a 0 = 0) (hK : a (K+1) = 0)
    {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    height (finiteOddProfile K a) (cos θ) =
      ∑ r ∈ Finset.range (K+1), primitiveCoefficient a r * sin ((2*(r:ℝ)+1)*θ) := by
  let f := finiteOddProfile K a
  rw [height_eq_integral_of_odd (profile_continuous K a) (profile_odd K a) (profile_zero K a),
    ← primitiveCoefficients K a ha hK]
  have h := intervalIntegral.integral_comp_mul_deriv (a:=0) (b:=θ) (g:=f)
    (fun x _ => Real.hasDerivAt_cos x) (continuous_sin.neg.continuousOn) (profile_continuous K a)
  simp only [Function.comp_apply, mul_neg, intervalIntegral.integral_neg, cos_zero] at h
  rw [intervalIntegral.integral_symm (cos θ) (1:ℝ) (f:=f)] at h
  trans ∫ t in 0..θ, f (cos t)*sin t
  · exact neg_inj.mp h.symm
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hθ.1] at ht
    dsimp [f]
    rw [profile_cos K a ⟨ht.1, ht.2.trans hθ.2⟩]

/-- The spectral definition of the first moment evaluates to πc₂/4. -/
theorem finiteOddProfile_mass (K : ℕ) (a : ℕ → ℝ) (ha : a 0 = 0) (hK : a (K+1) = 0) :
    mass (finiteOddProfile K a) = π / 4 * a 1 := by
  rw [mass, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    cosineSubstitution _ (height_continuous (profile_continuous K a).continuousOn), ← firstMomentPrimitive K a ha]
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le Real.pi_pos.le] at hθ
  dsimp only
  rw [finiteOddProfile_height_cos K a ha hK hθ]

/-- The primitive uses the frequencies 1, 3, …, 2K+1. -/
def primitiveFrequencies (K : ℕ) : Finset ℤ :=
  (Finset.range (K+1)).image (fun r : ℕ => 2*(r:ℤ)+1)

/-- Coefficients for the integer-indexed boundary and mass matrices. -/
def primitiveAmplitude (a : ℕ → ℝ) (j : ℤ) : ℝ :=
  primitiveCoefficient a ((j-1)/2).toNat

private theorem primitiveFrequencies_pos {K : ℕ} {j : ℤ} (hj : j ∈ primitiveFrequencies K) :
    0 < j := by
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hj
  omega

private theorem primitiveFrequencies_parity {K : ℕ} {i j : ℤ}
    (hi : i ∈ primitiveFrequencies K) (hj : j ∈ primitiveFrequencies K) : Even (i-j) := by
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hj
  exact ⟨(r:ℤ)-t, by ring⟩

private theorem primitiveSum (K : ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    (∑ j ∈ primitiveFrequencies K, primitiveAmplitude a j * sin ((j:ℝ)*θ)) =
      ∑ r ∈ Finset.range (K+1), primitiveCoefficient a r * sin ((2*(r:ℝ)+1)*θ) := by
  unfold primitiveFrequencies
  rw [Finset.sum_image (fun i _ j _ h => by omega)]
  apply Finset.sum_congr rfl
  intro i hi
  simp [primitiveAmplitude]

/-- The height in the spectral definitions is precisely the zero-exterior
profile used as density in the finite Cauchy integral. -/
theorem finiteOddProfile_height (K : ℕ) (a : ℕ → ℝ) (ha : a 0 = 0) (hK : a (K+1) = 0) :
    height (finiteOddProfile K a) = traceHeight (primitiveFrequencies K) (primitiveAmplitude a) := by
  funext x
  by_cases hx : |x| ≤ 1
  · have h := finiteOddProfile_height_cos K a ha hK (θ := arccos x) ⟨arccos_nonneg _, arccos_le_pi _⟩
    rw [cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2, ← primitiveSum] at h
    exact h
  · have hn : ¬ |x| < 1 := fun h => hx h.le
    rcases le_abs.mp (le_of_not_ge hx) with h | h
    · simp [height, hn, traceHeight, arccos_of_one_le h]
    · simp [height, hn, traceHeight, arccos_of_le_neg_one (by linarith : x ≤ -1), sin_int_mul_pi]

/-- The true second moment N equals the mass-matrix quadratic form of the
finite primitive coefficients. -/
theorem finiteOddProfile_squareMass (K : ℕ) (a : ℕ → ℝ) (ha : a 0 = 0) (hK : a (K+1) = 0) :
    squareMass (finiteOddProfile K a) =
      ∑ i ∈ primitiveFrequencies K, ∑ j ∈ primitiveFrequencies K, primitiveAmplitude a i *
        (1/(1-((i:ℝ)-j)^2)-1/(1-((i:ℝ)+j)^2)) * primitiveAmplitude a j := by
  rw [squareMass, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    cosineSubstitution (fun t => height (finiteOddProfile K a) t ^ 2)
      ((height_continuous (profile_continuous K a).continuousOn).pow 2),
    ← squareMoment (primitiveFrequencies K) (primitiveAmplitude a) (fun _ hi _ hj => primitiveFrequencies_parity hi hj)]
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le Real.pi_pos.le] at hθ
  dsimp only
  rw [finiteOddProfile_height_cos K a ha hK hθ, primitiveSum]

/-- The complex Cauchy extension of the actual finite trial profile
has the reconstructed Section 7 boundary coordinates. -/
theorem finiteOddProfile_cauchyTrace (K : ℕ) (a : ℕ → ℝ) (ha : a 0 = 0) (hK : a (K+1) = 0)
    {x : ℝ} (hx : |x| ≤ 1) :
    cauchyExtension (finiteOddProfile K a) x =
      (traceReal (primitiveFrequencies K) (primitiveAmplitude a) x : ℂ) +
        (height (finiteOddProfile K a) x : ℂ) * Complex.I := by
  rw [cauchyExtension, finiteOddProfile_height K a ha hK]
  exact finite_cauchyTrace _ _ (fun _ hj => primitiveFrequencies_pos hj) hx

end Torsion.Galerkin

module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Tactic

/-! # Exact sine-mode integrals for the odd Chebyshev Galerkin scheme -/

@[expose] public section

open Real MeasureTheory
open scoped Interval

namespace Torsion.Galerkin

/-- A primitive of the even-frequency product used in the mass formula. -/
private theorem weightedCosine (n : ℤ) :
    (∫ x in 0..π, sin x * cos ((2 * (n : ℝ)) * x)) = 2 / (1 - (2 * (n : ℝ)) ^ 2) := by
  let w : ℝ := 2 * (n : ℝ)
  have hw : w ^ 2 - 1 ≠ 0 := by
    dsimp [w]
    have h₁ : (2 : ℝ) * n ≠ 1 := by exact_mod_cast (by omega : 2 * n ≠ 1)
    have h₂ : (2 : ℝ) * n ≠ -1 := by exact_mod_cast (by omega : 2 * n ≠ -1)
    intro h
    rcases mul_eq_zero.mp (show (2 * (n : ℝ) - 1) * (2 * n + 1) = 0 by nlinarith) with h | h
    · exact h₁ (by linarith)
    · exact h₂ (by linarith)
  let F : ℝ → ℝ := fun x => (w * sin x * sin (w * x) + cos x * cos (w * x)) / (w ^ 2 - 1)
  have hd (x : ℝ) : HasDerivAt F (sin x * cos (w*x)) x := by
    have hlin : HasDerivAt (fun t : ℝ => w*t) w x := by simpa using (hasDerivAt_id x).const_mul w
    have h := ((((Real.hasDerivAt_sin x).const_mul w).mul hlin.sin).add
      ((Real.hasDerivAt_cos x).mul hlin.cos)).div_const (w ^ 2 - 1)
    convert h using 1
    field_simp
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := π) (fun x _ => hd x)
    ((show Continuous (fun x : ℝ => sin x * cos (w*x)) by fun_prop).intervalIntegrable _ _)
  have hπ : cos (w * π) = 1 := by
    rw [show w * π = (n : ℝ) * (2 * π) by dsimp [w]; ring, Real.cos_int_mul_two_pi]
  change (∫ x in 0..π, sin x * cos (w*x)) = 2 / (1-w^2)
  rw [he]
  simp only [F, sin_pi, cos_pi, hπ, mul_zero, sin_zero, cos_zero, zero_mul, zero_add, mul_one]
  have hw' : 1-w^2 ≠ 0 := by intro h; apply hw; linarith
  field_simp
  ring

/-- Mass in the sine-coordinate representation.  Equal parity covers both the
even trial frequencies and the odd frequencies of their primitives. -/
theorem weightedSineMass (k l : ℤ) (hpar : Even (k-l)) :
    (∫ x in 0..π, sin ((k : ℝ)*x) * sin ((l : ℝ)*x) * sin x) =
      1 / (1-((k : ℝ)-l)^2) - 1 / (1-((k : ℝ)+l)^2) := by
  obtain ⟨n,hn⟩ := hpar
  have hm : (k : ℝ) - l = 2 * (n : ℝ) := by exact_mod_cast (by omega : k-l=2*n)
  have hp : (k : ℝ) + l = 2 * ((n+l : ℤ) : ℝ) := by exact_mod_cast (by omega : k+l=2*(n+l))
  let G (n : ℤ) (x : ℝ) := sin x * cos ((2*(n : ℝ))*x)
  have hi (n : ℤ) : IntervalIntegrable (G n) volume 0 π :=
    (show Continuous (G n) by dsimp [G]; fun_prop).intervalIntegrable _ _
  have he (x : ℝ) :
      sin ((k : ℝ)*x) * sin ((l : ℝ)*x) * sin x = (G n x-G (n+l) x) / 2 := by
    have h := Real.two_mul_sin_mul_sin ((k : ℝ)*x) ((l : ℝ)*x)
    rw [← sub_mul, ← add_mul, hm,hp] at h
    dsimp [G]
    linear_combination sin x / 2 * h
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hi _) (hi _)]
  dsimp [G]
  rw [weightedCosine, weightedCosine, hm,hp]
  ring

/-- The zero-exterior basis restricted to its support, in Chebyshev coordinates. -/
theorem chebyshevSine (k : ℤ) {x : ℝ} (h₁ : -1 ≤ x) (h₂ : x ≤ 1) :
    Real.sqrt (1-x^2) * (Polynomial.Chebyshev.U ℝ (k-1)).eval x = sin ((k : ℝ)*arccos x) := by
  have h := Polynomial.Chebyshev.U_real_cos (arccos x) (k-1)
  rw [Real.cos_arccos h₁ h₂, Real.sin_arccos] at h
  convert h using 1 <;> push_cast <;> ring_nf

/-- The primitive of one even trial mode has just two neighboring odd modes. -/
theorem sineModePrimitive (k θ : ℝ) (hk : 1 < k) :
    (∫ x in 0..θ, sin (k*x)*sin x) =
     sin ((k-1)*θ)/(2*(k-1)) - sin ((k+1)*θ)/(2*(k+1)) := by
  let F : ℝ → ℝ := fun x => sin ((k-1)*x)/(2*(k-1)) - sin ((k+1)*x)/(2*(k+1))
  have hd (x : ℝ) : HasDerivAt F (sin (k*x)*sin x) x := by
    have hlin (z : ℝ) : HasDerivAt (fun t : ℝ => z*t) z x := by simpa using (hasDerivAt_id x).const_mul z
    have h := (((hlin (k-1)).sin).div_const (2*(k-1))).sub
      (((hlin (k+1)).sin).div_const (2*(k+1)))
    convert h using 1
    have ht := Real.two_mul_sin_mul_sin (k*x) x
    rw [show k*x-x=(k-1)*x by ring, show k*x+x=(k+1)*x by ring] at ht
    have hm : k - 1 ≠ 0 := by linarith
    have hp : k + 1 ≠ 0 := by linarith
    have hc (a b : ℝ) (hb : b ≠ 0) : a*b/(2*b) = a/2 := by field_simp
    rw [hc _ _ hm, hc _ _ hp]
    linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((show Continuous (fun x : ℝ => sin (k*x)*sin x) by fun_prop).intervalIntegrable _ _)]
  simp [F]

/-- Exact quadratic moment for any finite set of primitive frequencies of the same parity. -/
theorem squareMoment (s : Finset ℤ) (d : ℤ → ℝ) (hp : ∀ i ∈ s, ∀ j ∈ s, Even (i-j)) :
    (∫ x in 0..π, (∑ i ∈ s, d i*sin ((i : ℝ)*x))^2 * sin x) =
    ∑ i ∈ s, ∑ j ∈ s, d i * (1/(1-((i:ℝ)-j)^2)-1/(1-((i:ℝ)+j)^2)) * d j := by
  let F (i j : ℤ) (x : ℝ) := (d i * d j) * (sin ((i:ℝ)*x)*sin ((j:ℝ)*x)*sin x)
  have hC (i j : ℤ) : Continuous (F i j) := by dsimp [F]; fun_prop
  have he (x : ℝ) : (∑ i ∈ s, d i * sin ((i:ℝ)*x))^2 * sin x = ∑ i ∈ s, ∑ j ∈ s, F i j x := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [F]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun i _ => (continuous_finsetSum _ fun j _ => hC i j).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hC i j).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [F]
  rw [intervalIntegral.integral_const_mul, weightedSineMass i j (hp i hi j hj)]
  ring

private theorem integerCosineIntegral (n : ℤ) :
    (∫ x in 0..π, cos ((n : ℝ)*x)) = if n=0 then π else 0 := by
  by_cases hn : n=0
  · simp [hn]
  · rw [ite_eq_right hn]
    have h := intervalIntegral.mul_integral_comp_mul_left (a := 0) (b := π) (f := cos) (n:ℝ)
    simp only [mul_zero, integral_cos, sin_int_mul_pi, sin_zero, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)

/-- Unweighted sine orthogonality on the half circle. -/
theorem sineOrthogonality (k l : ℤ) (hk : 0 < k) (hl : 0 < l) :
    (∫ x in 0..π, sin ((k:ℝ)*x)*sin ((l:ℝ)*x)) = if k=l then π/2 else 0 := by
  have he (x : ℝ) : sin ((k:ℝ)*x)*sin ((l:ℝ)*x) =
      (cos (((k-l : ℤ):ℝ)*x)-cos (((k+l : ℤ):ℝ)*x))/2 := by
    push_cast
    rw [sub_mul, add_mul]
    linarith [Real.two_mul_sin_mul_sin ((k:ℝ)*x) ((l:ℝ)*x)]
  have hi (m : ℤ) : IntervalIntegrable (fun x : ℝ => cos ((m:ℝ)*x)) volume 0 π :=
    (show Continuous (fun x : ℝ => cos ((m:ℝ)*x)) by fun_prop).intervalIntegrable _ _
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hi _) (hi _),
      integerCosineIntegral, integerCosineIntegral, ite_eq_right (by omega : k+l ≠ 0)]
  by_cases h : k=l <;> simp [h, sub_eq_zero]

/-- The first moment is precisely the coefficient of frequency one. -/
theorem firstMoment (s : Finset ℤ) (hs : ∀ i ∈ s, 0 < i) (h1 : 1 ∈ s) (d : ℤ → ℝ) :
    (∫ x in 0..π, (∑ i ∈ s, d i*sin ((i:ℝ)*x))*sin x) = π/2*d 1 := by
  have hi (i : ℤ) : IntervalIntegrable (fun x : ℝ => d i * sin ((i:ℝ)*x) * sin x) volume 0 π :=
    (show Continuous (fun x : ℝ => d i * sin ((i:ℝ)*x)*sin x) by fun_prop).intervalIntegrable _ _
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  calc
    _ = ∑ i ∈ s, if i=1 then d i*(π/2) else 0 := by
      apply Finset.sum_congr rfl
      intro i his
      simp_rw [mul_assoc]
      rw [intervalIntegral.integral_const_mul]
      have hh := sineOrthogonality i 1 (hs i his) (by decide)
      simp only [Int.cast_one,one_mul] at hh
      rw [hh]
      split_ifs <;> simp
    _ = _ := by simp [h1, mul_comm]

/-- Cosine substitution for continuous functions of the physical interval. -/
theorem cosineSubstitution (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (-1 : ℝ)..1, f t) = ∫ x in 0..π, f (cos x)*sin x := by
  have h := intervalIntegral.integral_comp_mul_deriv (a:=0) (b:=π) (g:=f)
    (fun x _ => Real.hasDerivAt_cos x) (continuous_sin.neg.continuousOn) hf
  simp only [Function.comp_apply, mul_neg, intervalIntegral.integral_neg, cos_zero, cos_pi] at h
  rw [intervalIntegral.integral_symm (-1:ℝ) 1 (f := f)] at h
  linarith

/-- Odd sine coefficient of the integrated trial mode, with index `r`
corresponding to manuscript frequency `2r+1` and `a r` to `c_(2r)`. -/
noncomputable def primitiveCoefficient (a : ℕ → ℝ) (r : ℕ) : ℝ :=
  (a (r+1)-a r)/(2*(2*r+1))

/-- Integration of any truncated even-frequency trial polynomial gives
the exact adjacent-coefficient formula, including both end modes. -/
theorem primitiveCoefficients (K : ℕ) (a : ℕ → ℝ) (ha : a 0=0) (hK : a (K+1)=0) (θ : ℝ) :
    (∫ x in 0..θ, (∑ r ∈ Finset.range K, a (r+1)*sin ((2*(r:ℝ)+2)*x))*sin x) =
      ∑ r ∈ Finset.range (K+1), primitiveCoefficient a r * sin ((2*(r:ℝ)+1)*θ) := by
  let F (r : ℕ) := sin ((2*(r:ℝ)+1)*θ)/(2*(2*r+1))
  have hi (r : ℕ) : IntervalIntegrable (fun x : ℝ => a (r+1)*sin ((2*(r:ℝ)+2)*x)*sin x)
      volume 0 θ := (show Continuous _ by fun_prop).intervalIntegrable _ _
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun r _ => hi r)]
  have he (r : ℕ) :
      (∫ x in 0..θ, a (r+1)*sin ((2*(r:ℝ)+2)*x)*sin x) =
        a (r+1)*F r - a (r+1)*F (r+1) := by
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, sineModePrimitive (2*(r:ℝ)+2) θ (by have := Nat.cast_nonneg (α:=ℝ) r; linarith)]
    dsimp [F]
    push_cast
    ring_nf
  simp_rw [he, Finset.sum_sub_distrib]
  have reindex : ∀ r : ℕ, primitiveCoefficient a r * sin ((2*(r:ℝ)+1)*θ) =
      a (r+1)*F r - a r*F r := by
    intro r
    dsimp [primitiveCoefficient,F]
    ring
  simp_rw [reindex,Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ (f := fun r => a (r+1)*F r),
      Finset.sum_range_succ' (f := fun r => a r*F r)]
  simp [ha,hK]

/-- The physical-interval Gram integral, after the actual cosine change of variables. -/
theorem physicalMass (k l : ℤ) (hp : Even (k-l)) :
    (∫ t in (-1:ℝ)..1, sin ((k:ℝ)*arccos t) * sin ((l:ℝ)*arccos t)) =
      1/(1-((k:ℝ)-l)^2) - 1/(1-((k:ℝ)+l)^2) := by
  rw [cosineSubstitution _ (by fun_prop), ← weightedSineMass k l hp]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le Real.pi_pos.le] at hx
  simp [Real.arccos_cos hx.1 hx.2]

/-- The actual first moment of the primitive expansion, with the manuscript's
normalization `M = π c₂ / 4`. -/
theorem firstMomentPrimitive (K : ℕ) (a : ℕ → ℝ) (ha : a 0=0) :
    (∫ x in 0..π, (∑ r ∈ Finset.range (K+1), primitiveCoefficient a r *
      sin ((2*(r:ℝ)+1)*x))*sin x) = π/4*a 1 := by
  let f (r : ℕ) (x : ℝ) := primitiveCoefficient a r * sin ((2*(r:ℝ)+1)*x) * sin x
  have hi (r : ℕ) : IntervalIntegrable (f r) volume 0 π :=
    (show Continuous (f r) by dsimp [f]; fun_prop).intervalIntegrable _ _
  simp_rw [Finset.sum_mul]
  change (∫ x in 0..π, ∑ r ∈ Finset.range (K+1), f r x) = _
  rw [intervalIntegral.integral_finsetSum (fun r _ => hi r)]
  have h (r : ℕ) : (∫ x in 0..π, f r x) = if r=0 then π/4*a 1 else 0 := by
    dsimp only [f]
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    have hh := sineOrthogonality (2*(r:ℤ)+1) 1 (by omega) (by decide)
    push_cast at hh
    simp only [one_mul] at hh
    rw [hh]
    by_cases hr : r=0
    · subst r
      simp [primitiveCoefficient,ha]
      ring
    · have hn : 2*(r:ℤ)+1 ≠ 1 := by omega
      simp [hn,hr]
  simp_rw [h]
  simp

/-- The exact Green area integral of a finite sine/cosine boundary trace.
The second factor is the angular derivative of the negative cosine trace. -/
theorem sineTraceArea (s : Finset ℤ) (d : ℤ → ℝ) (hs : ∀ i ∈ s, 0 < i) :
    (∫ x in 0..π, (∑ i ∈ s, d i*sin ((i:ℝ)*x)) *
      (∑ j ∈ s, (j:ℝ)*d j*sin ((j:ℝ)*x))) =
      π/2 * ∑ i ∈ s, (i:ℝ)*(d i)^2 := by
  let f (i j : ℤ) (x : ℝ) :=
    (d i * ((j:ℝ)*d j)) * (sin ((i:ℝ)*x)*sin ((j:ℝ)*x))
  have hC (i j : ℤ) : Continuous (f i j) := by dsimp [f]; fun_prop
  have he (x : ℝ) :
      (∑ i ∈ s, d i*sin ((i:ℝ)*x)) * (∑ j ∈ s, (j:ℝ)*d j*sin ((j:ℝ)*x)) =
      ∑ i ∈ s, ∑ j ∈ s, f i j x := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [f]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun i _ => (continuous_finsetSum _ fun j _ => hC i j).intervalIntegrable _ _),
      Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hC i j).intervalIntegrable _ _)]
  calc
    _ = ∑ j ∈ s, if i=j then d i * ((j:ℝ)*d j) * (π/2) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [f]
      rw [intervalIntegral.integral_const_mul, sineOrthogonality i j (hs _ hi) (hs _ hj)]
      split_ifs <;> simp
    _ = _ := by simp [hi]; ring

/-- The energy-side integral after the Chebyshev operator formula
`L ψₖ = k Uₖ₋₁`: sine orthogonality makes the resulting matrix diagonal. -/
theorem chebyshevEnergyIntegral (k l : ℤ) (hk : 0 < k) (hl : 0 < l) :
    (∫ t in (-1:ℝ)..1, (k:ℝ) * (Polynomial.Chebyshev.U ℝ (k-1)).eval t *
      sin ((l:ℝ)*arccos t)) = if k=l then (k:ℝ)*π/2 else 0 := by
  have hcont : Continuous (fun t : ℝ => (k:ℝ) * (Polynomial.Chebyshev.U ℝ (k-1)).eval t *
      sin ((l:ℝ)*arccos t)) := by fun_prop
  rw [cosineSubstitution _ hcont]
  calc
    _ = ∫ x in 0..π, (k:ℝ) * (sin ((k:ℝ)*x)*sin ((l:ℝ)*x)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le Real.pi_pos.le] at hx
      simp only [Real.arccos_cos hx.1 hx.2]
      have h := Polynomial.Chebyshev.U_real_cos x (k-1)
      push_cast at h
      rw [sub_add_cancel] at h
      linear_combination (k:ℝ)*sin ((l:ℝ)*x)*h
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, sineOrthogonality k l hk hl]
      split_ifs <;> ring

/-- Real coordinate of the finite boundary trace in its original parameter. -/
noncomputable def traceReal (s : Finset ℤ) (d : ℤ → ℝ) (t : ℝ) : ℝ :=
  -(∑ j ∈ s, d j * (Polynomial.Chebyshev.T ℝ j).eval t)

/-- Height coordinate of the finite boundary trace. -/
noncomputable def traceHeight (s : Finset ℤ) (d : ℤ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ s, d j * sin ((j:ℝ)*arccos t)

/-- The signed area of the reconstructed Chebyshev boundary, expressed
using the genuine derivative of its polynomial real coordinate. -/
theorem physicalTraceArea (s : Finset ℤ) (d : ℤ → ℝ) (hs : ∀ i ∈ s, 0 < i) :
    -(∫ t in (-1:ℝ)..1, traceHeight s d t * deriv (traceReal s d) t) =
        π/2 * ∑ j ∈ s, (j:ℝ)*(d j)^2 := by
  let U (j : ℤ) (t : ℝ) := (Polynomial.Chebyshev.U ℝ (j-1)).eval t
  have hx (t : ℝ) : deriv (traceReal s d) t = -(∑ j ∈ s, d j * ((j:ℝ) * U j t)) := by
    apply HasDerivAt.deriv
    apply HasDerivAt.neg
    apply HasDerivAt.fun_sum
    intro j hj
    have h := ((Polynomial.Chebyshev.T ℝ j).hasDerivAt t).const_mul (d j)
    simpa [U, Polynomial.Chebyshev.T_derivative_eq_U] using h
  simp_rw [hx, mul_neg, intervalIntegral.integral_neg, neg_neg]
  have hc : Continuous (fun t : ℝ => traceHeight s d t * ∑ j ∈ s, d j * ((j:ℝ)*U j t)) := by
    dsimp [traceHeight,U]
    fun_prop
  rw [cosineSubstitution _ hc, ← sineTraceArea s d hs]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le Real.pi_pos.le] at hx
  dsimp only [traceHeight]
  rw [Real.arccos_cos hx.1 hx.2, mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have h := Polynomial.Chebyshev.U_real_cos x (j-1)
  push_cast at h
  rw [sub_add_cancel] at h
  dsimp [U]
  linear_combination (d j * (j:ℝ))*h

end Torsion.Galerkin

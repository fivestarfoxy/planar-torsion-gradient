module

public import Torsion.Proof.PaperBrownianModel

@[expose] public section

/-! # Finite expected lifetime in every bounded planar set

Survival up to integer time n forces its n real coordinate increments to stay
in a fixed Gaussian half-line. Independence gives a geometric majorant for
the lifetime. This estimate also bounds the upper lifetime on sample paths
before measurability of a particular boundary is considered.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace Torsion.Brownian
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private abbrev increment (B : ℝ≥0 → Ω → Plane) (i : ℕ) (ω : Ω) :=
  (B (i+1 : ℕ) ω).re - (B i ω).re

private def good (B : ℝ≥0 → Ω → Plane) (R : ℝ) (n : ℕ) : Set Ω :=
  ⋂ i ∈ Finset.range n, increment B i ⁻¹' Iic (2*R)

private theorem good_probability {B : ℝ≥0 → Ω → Plane} (hB : IsPlanarBrownian B P)
    (R : ℝ) (n : ℕ) :
    P (good B R n) = (gaussianReal 0 1 (Iic (2*R))) ^ n := by
  have hi := hB.re.hasIndepIncrements.nat (t := fun i : ℕ => (i : ℝ≥0))
    (fun i j h => Nat.cast_le.mpr h)
  have hm (i : ℕ) : P (increment B i ⁻¹' Iic (2*R)) = gaussianReal 0 1 (Iic (2*R)) := by
    have hl := hB.re.hasLaw_sub (i+1 : ℕ) i
    have ht : nndist (((i+1 : ℕ):ℝ≥0):ℝ) ((i:ℝ≥0):ℝ) = 1 := by
      apply NNReal.eq
      simp [dist_eq_norm]
    have hform : HasLaw (increment B i) (gaussianReal 0 (nndist (((i+1 : ℕ):ℝ≥0):ℝ) ((i:ℝ≥0):ℝ))) P := hl
    rw [ht] at hform
    exact hform.measure_eq (p := fun y => y ≤ 2*R) measurableSet_Iic
  calc
    P (good B R n) = ∏ i ∈ Finset.range n, P (increment B i ⁻¹' Iic (2*R)) :=
      hi.meas_biInter fun i _ => ⟨Iic (2*R), measurableSet_Iic, rfl⟩
    _ = _ := by simp [hm]

private theorem gaussian_probability_lt_one (R : ℝ) :
    gaussianReal 0 1 (Iic (2*R)) < 1 := by
  refine lt_of_le_of_ne prob_le_one ?_
  intro h
  have he := prob_compl_eq_one_sub (μ := gaussianReal 0 1) (measurableSet_Iic (a := 2*R))
  rw [h, tsub_self, compl_Iic] at he
  have habs := gaussianReal_absolutelyContinuous' 0 (v := 1) one_ne_zero he
  simp at habs

private theorem good_nullMeasurable {B : ℝ≥0 → Ω → Plane} (hB : IsPlanarBrownian B P) (R : ℝ) (n : ℕ) :
    NullMeasurableSet (good B R n) P := by
  exact (Finset.range n).nullMeasurableSet_biInter fun i _ =>
    ((hB.re.aemeasurable (i+1 : ℕ)).sub (hB.re.aemeasurable i)).nullMeasurableSet_preimage measurableSet_Iic

omit [MeasurableSpace Ω] in
private theorem exit_le_majorant {D : Set Plane} {R : ℝ} (hR : ∀ z ∈ D, ‖z‖ ≤ R)
    (x : Plane) (B : ℝ≥0 → Ω → Plane) (ω : Ω) :
    exitTime D x B ω ≤ ∑' n, (good B R n).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  classical
  by_cases hx : ∀ n : ℕ, ω ∈ good B R n
  · simp only [Set.indicator_of_mem (hx _), ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero, le_top]
  push Not at hx
  let n := Nat.find hx
  have hbad : ω ∉ good B R n := Nat.find_spec hx
  have hτ : exitTime D x B ω ≤ n := by
    by_contra! hs
    apply hbad
    apply mem_iInter₂.mpr
    intro i hi
    have hin := Finset.mem_range.mp hi
    have hprev : ((i : ℝ≥0) : ℝ≥0∞) < exitTime D x B ω := lt_trans (by exact_mod_cast hin) hs
    have hnext : (((i+1 : ℕ) : ℝ≥0) : ℝ≥0∞) < exitTime D x B ω :=
      lt_of_le_of_lt (by exact_mod_cast hin) hs
    have h1 := hR _ (mem_of_lt_exitTime hprev)
    have h2 := hR _ (mem_of_lt_exitTime hnext)
    have hr1 := (neg_le_abs (x + B i ω).re).trans ((Complex.abs_re_le_norm _).trans h1)
    have hr2 := (le_abs_self (x + B (i+1 : ℕ) ω).re).trans ((Complex.abs_re_le_norm _).trans h2)
    change (B (i+1 : ℕ) ω).re - (B i ω).re ≤ 2*R
    simp only [Complex.add_re] at hr1 hr2
    linarith
  apply hτ.trans
  apply le_trans _ (ENNReal.sum_le_tsum (Finset.range n))
  have he i (hi : i ∈ Finset.range n) : ω ∈ good B R i := by
    by_contra h
    exact (not_lt_of_ge (Nat.find_min' hx h)) (Finset.mem_range.mp hi)
  rw [Finset.sum_congr rfl (fun i hi => Set.indicator_of_mem (he i hi) _)]
  simp

/-- In any bounded set the actual continuous-time Brownian exit has a finite
nonnegative integral. The estimate holds even for an irregular set since the
geometric majorant is measurable up to null sets. -/
theorem IsPlanarBrownian.lintegral_exitTime_lt_top {B : ℝ≥0 → Ω → Plane} (hB : IsPlanarBrownian B P)
    {D : Set Plane} (hD : Bornology.IsBounded D) (x : Plane) : ∫⁻ ω, exitTime D x B ω ∂P < ⊤ := by
  obtain ⟨R, hR⟩ := hD.exists_norm_le
  calc
    _ ≤ ∫⁻ ω, ∑' n, (good B R n).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P :=
      lintegral_mono (exit_le_majorant hR x B)
    _ = ∑' n, (gaussianReal 0 1 (Iic (2*R))) ^ n := by
      rw [lintegral_tsum (fun n => aemeasurable_const.indicator₀ (good_nullMeasurable hB R n))]
      congr 1
      funext n
      rw [lintegral_indicator₀ (good_nullMeasurable hB R n), setLIntegral_const, one_mul,
        good_probability hB]
    _ < ⊤ := by rw [ENNReal.tsum_geometric]; exact ENNReal.inv_lt_top.mpr (tsub_pos_of_lt (gaussian_probability_lt_one R))

end Torsion.Brownian

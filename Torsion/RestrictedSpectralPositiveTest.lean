module

public import Torsion.RestrictedSpectralCoreDirections
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual positive odd tests and compact positive-interval selection

The test is x times a genuine smooth even bump with an explicit plateau
covering the selected positive rectangle. It belongs to the original core,
is odd, equals x on the plateau, and has a global bound of one.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- A genuine smooth even bump with plateau radius R and support radius
strictly between R and the original interval endpoint. -/
def oddPlateauBump (R : ℝ) (hR0 : 0 < R) (hR1 : R < 1) : ContDiffBump (0 : ℝ) :=
  ⟨R, (R + 1) / 2, hR0, by linarith⟩

/-- The actual smooth odd positive test used in the half-line variational
perturbation. -/
def oddPlateauTest (R : ℝ) (hR0 : 0 < R) (hR1 : R < 1) (x : ℝ) : ℝ :=
  x * oddPlateauBump R hR0 hR1 x

theorem oddPlateauTest_isCore (R : ℝ) (hR0 : 0 < R) (hR1 : R < 1) :
    IsCore (oddPlateauTest R hR0 hR1) := by
  refine ⟨contDiff_id.mul (oddPlateauBump R hR0 hR1).contDiff,
    (oddPlateauBump R hR0 hR1).hasCompactSupport.mul_left, ?_⟩
  apply tsupport_mul_subset_right.trans
  rw [(oddPlateauBump R hR0 hR1).tsupport_eq]
  intro x hx
  have h : |x| ≤ (R + 1) / 2 := by simpa [oddPlateauBump, Real.dist_eq] using hx
  have hh := abs_le.1 h
  constructor <;> linarith [hh.1, hh.2]

theorem oddPlateauTest_odd (R : ℝ) (hR0 : 0 < R) (hR1 : R < 1) :
    Function.Odd (oddPlateauTest R hR0 hR1) := by
  intro x
  simp only [oddPlateauTest, (oddPlateauBump R hR0 hR1).neg x]
  ring

theorem oddPlateauTest_eq_id (R : ℝ) (hR0 : 0 < R) (hR1 : R < 1)
    {x : ℝ} (hx : |x| ≤ R) : oddPlateauTest R hR0 hR1 x = x := by
  rw [oddPlateauTest, (oddPlateauBump R hR0 hR1).one_of_mem_closedBall]
  · exact mul_one x
  · simpa [oddPlateauBump, Real.dist_eq] using hx

/-- The test has a uniform global bound, including outside its support. -/
theorem oddPlateauTest_abs_le_one (R : ℝ) (hR0 : 0 < R) (hR1 : R < 1) (x : ℝ) :
    |oddPlateauTest R hR0 hR1 x| ≤ 1 := by
  by_cases hx : |x| ≤ 1
  · rw [oddPlateauTest, abs_mul,
      abs_of_nonneg (oddPlateauBump R hR0 hR1).nonneg]
    calc
      |x| * oddPlateauBump R hR0 hR1 x ≤ 1 * 1 :=
        mul_le_mul hx (oddPlateauBump R hR0 hR1).le_one
          (oddPlateauBump R hR0 hR1).nonneg (by norm_num)
      _ = 1 := by norm_num
  · have hzero : oddPlateauBump R hR0 hR1 x = 0 :=
      (oddPlateauBump R hR0 hR1).zero_of_le_dist (by
        change (R + 1) / 2 ≤ dist x 0
        simpa only [dist_zero_right, Real.norm_eq_abs] using
          (show (R + 1) / 2 ≤ |x| from by linarith [le_of_not_ge hx]))
    simp [oddPlateauTest, hzero]

/-- On a positive rectangle inside the plateau the lower and upper bounds
needed by the quantitative odd-fold gap are actual proved estimates. -/
theorem oddPlateauTest_rectangle_bounds (R : ℝ) (hR0 : 0 < R) (hR1 : R < 1)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Icc r R) :
    r ≤ oddPlateauTest R hR0 hR1 x ∧ |oddPlateauTest R hR0 hR1 x| ≤ 1 := by
  refine ⟨?_, oddPlateauTest_abs_le_one R hR0 hR1 x⟩
  rw [oddPlateauTest_eq_id R hR0 hR1 (by rw [abs_of_pos (hr.trans_le hx.1)]; exact hx.2)]
  exact hx.1

/-- There is a genuine odd original-core test equal to the identity on
any specified compact symmetric subinterval of (-1,1). -/
theorem exists_odd_core_eq_id_on_Icc (R : ℝ) (hR0 : 0 < R) (hR1 : R < 1) :
    ∃ ψ : ℝ → ℝ, IsCore ψ ∧ Function.Odd ψ ∧
      (∀ x : ℝ, |x| ≤ R → ψ x = x) ∧ (∀ x : ℝ, |ψ x| ≤ 1) :=
  ⟨oddPlateauTest R hR0 hR1, oddPlateauTest_isCore R hR0 hR1,
    oddPlateauTest_odd R hR0 hR1,
    (fun _ hx => oddPlateauTest_eq_id R hR0 hR1 hx), oddPlateauTest_abs_le_one R hR0 hR1⟩

/-- Every non-null subset of the positive interval has a non-null portion
inside a compact interval staying strictly away from both endpoints. No
measurability assumption is needed for this outer-measure selection. -/
theorem exists_positive_compact_interval_inter_measure_ne_zero {A : Set ℝ}
    (hsubset : A ⊆ Ioo (0 : ℝ) 1) (hA : volume A ≠ 0) :
    ∃ r R : ℝ, 0 < r ∧ R < 1 ∧ volume (A ∩ Icc r R) ≠ 0 := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let S : ℕ → Set ℝ := fun n => A ∩ Icc (r n) (1 - r n)
  have hcover : A ⊆ ⋃ n : ℕ, S n := by
    intro x hx
    have hxi := hsubset hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hxi.1 (sub_pos.2 hxi.2))
    apply mem_iUnion.2
    refine ⟨n, hx, ?_, ?_⟩
    · exact hn.le.trans (min_le_left _ _)
    · have h := hn.trans_le (min_le_right x (1 - x))
      change x ≤ 1 - 1 / ((n : ℝ) + 1)
      linarith
  have hUnion : volume (⋃ n : ℕ, S n) ≠ 0 := by
    intro hz
    exact hA (measure_mono_null hcover hz)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hUnion
  refine ⟨r n, 1 - r n, ?_, ?_, hn.ne'⟩
  · dsimp [r]
    positivity
  · have hp : 0 < r n := by dsimp [r]; positivity
    linarith

/-- Two non-null positive-interval sets have non-null portions inside one
common compact positive interval, allowing the same plateau test and the
same quantitative kernel bound for the two rectangle factors. -/
theorem exists_common_positive_compact_interval_inter_measure_ne_zero {A B : Set ℝ}
    (hAsub : A ⊆ Ioo (0 : ℝ) 1) (hA : volume A ≠ 0)
    (hBsub : B ⊆ Ioo (0 : ℝ) 1) (hB : volume B ≠ 0) :
    ∃ r R : ℝ, 0 < r ∧ 0 < R ∧ R < 1 ∧
      volume (A ∩ Icc r R) ≠ 0 ∧ volume (B ∩ Icc r R) ≠ 0 := by
  obtain ⟨rA, RA, hrA, hRA, hmA⟩ :=
    exists_positive_compact_interval_inter_measure_ne_zero hAsub hA
  obtain ⟨rB, RB, hrB, hRB, hmB⟩ :=
    exists_positive_compact_interval_inter_measure_ne_zero hBsub hB
  obtain ⟨z, hz⟩ := nonempty_of_measure_ne_zero hmA
  refine ⟨min rA rB, max RA RB, lt_min hrA hrB, ?_, max_lt hRA hRB, ?_, ?_⟩
  · exact (hrA.trans_le (hz.2.1.trans hz.2.2)).trans_le (le_max_left RA RB)
  · intro hzero
    apply hmA
    apply measure_mono_null ?_ hzero
    intro x hx
    exact ⟨hx.1, (min_le_left rA rB).trans hx.2.1, hx.2.2.trans (le_max_left RA RB)⟩
  · intro hzero
    apply hmB
    apply measure_mono_null ?_ hzero
    intro x hx
    exact ⟨hx.1, (min_le_right rA rB).trans hx.2.1, hx.2.2.trans (le_max_right RA RB)⟩

end Torsion.Spectral

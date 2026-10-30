module

public import Torsion.MarkedHullCollarComparison
public import Torsion.SupportedConvexFlatHullUniform
public import Torsion.FlatOuterHullArea

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A sharp uniform normal collar bound from the actual flat outer hull

An actual inball and a bound on its distance from a supporting point give
one flat patch for all supported coordinate frames. The hull area loss can
be made uniformly small; its fixed-patch torsion Taylor remainder can then
be made uniformly small by reducing the normal distance. All comparison
constants are constructed, and the canonical radial bound is used as proved.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Torsion
open Spectral

/-- A single normal collar works for every supported convex domain with
fixed area, inball radius, inball displacement bound and upper slab height.
The weak torsion value may be any actual continuous interior representative. -/
theorem exists_uniform_second_supported_normal_bound
    {A h M b : ℝ} (_hA : 0 ≤ A) (hh : 0 < h) (hM : 0 ≤ M) (hb : 0 ≤ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {D : ConvexDomain} {a : Plane}
      {u U : Plane → ℝ} {g : Plane → Plane},
      D.area = A → D.carrier ⊆ upperHalfPlane → (0 : Plane) ∈ closure D.carrier →
      a ∈ D.carrier → ball a h ⊆ D.carrier → h ≤ a.im → ‖a‖ ≤ M →
      (∀ z ∈ D.carrier, z.im ≤ b) →
      IsWeakTorsion D.carrier u g → ContinuousOn U D.carrier →
      (u =ᵐ[volume.restrict D.carrier] U) →
      ∀ t : ℝ, 0 < t → t < δ → (t : Plane)*Complex.I ∈ D.carrier →
        U ((t : Plane)*Complex.I) ≤
          (spectralConstant secondEigenvalue secondEigenfunction * Real.sqrt A + ε)*t := by
  let S := spectralConstant secondEigenvalue secondEigenfunction
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  let B : ℝ := S * Real.sqrt A
  have hB : 0 ≤ B := mul_nonneg hS (Real.sqrt_nonneg _)
  let r : ℝ := ε*h/(4*(B+1))
  have hr : 0 < r := div_pos (mul_pos hε hh) (by positivity)
  have hrid : 4*(B+1)*r = ε*h := by
    dsimp [r]
    field_simp
  have hrloss : (2*r/h)*B ≤ ε/2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hh]
    nlinarith
  let ρ := flatHullPatchRadius r h M / 4
  have hρ : 0 < ρ := div_pos (flatHullPatchRadius_pos hr hh hM) (by norm_num)
  obtain ⟨C, hC, hcompare⟩ := exists_uniform_second_spectral_collar_comparison_constant hρ
  let K : ℝ := C*(2*ρ*b+8*ρ^2)+1/2
  have hK : 0 < K := by dsimp [K]; positivity
  let δ : ℝ := min (ρ/2) (ε/(2*(K+1)))
  have hδ : 0 < δ := lt_min (half_pos hρ) (div_pos hε (by positivity))
  refine ⟨δ, hδ, ?_⟩
  intro D a u U g harea hhalf hzero ha hball hheight hnorm hupper hu hU hrep t ht htδ htD
  let E := D.flatHull r
  have hDE : D.carrier ⊆ E.carrier := subset_flatOuterHull D.isOpen r
  have hE : IsMarked E.carrier :=
    flatOuterHull_isMarked D.isOpen D.bounded hhalf D.nonempty hr
  have hpatch : upperHalfPlane ∩ ball (0 : Plane) (4*ρ) ⊆ E.carrier := by
    convert halfBall_subset_flatOuterHull_of_point_bounds D.isOpen ha hr hh hM hheight hnorm using 1
    dsimp [ρ]
    ring_nf
  have hEheight : ∀ z ∈ E.carrier, z.im < b :=
    flatOuterHull_subset_upper_height hb hupper r
  have htsmall : t < ρ/2 := htδ.trans_le (min_le_left _ _)
  have hpoint := hcompare hu hU hrep hDE hE hb hpatch hEheight t ht htsmall htD
  have hareaE : Real.sqrt E.area ≤ (1+2*r/h)*Real.sqrt A := by
    simpa only [harea] using D.flatHull_sqrt_area_le hh hball hzero hr
  have hspec : S * Real.sqrt E.area ≤ B + ε/2 := by
    calc
      S * Real.sqrt E.area ≤ S*((1+2*r/h)*Real.sqrt A) :=
        mul_le_mul_of_nonneg_left hareaE hS
      _ = B + (2*r/h)*B := by dsimp [B]; ring
      _ ≤ B + ε/2 := add_le_add_left hrloss B
  have htK : K*t ≤ ε/2 := by
    have htbound : t < ε/(2*(K+1)) := htδ.trans_le (min_le_right _ _)
    have hm := (lt_div_iff₀ (show 0 < 2*(K+1) by positivity)).mp htbound
    have hm' : 2*(K*t)+2*t < ε := by convert hm using 1; ring
    have hl : 2*(K*t) < ε :=
      (le_add_of_nonneg_right (show 0 ≤ 2*t by positivity)).trans_lt hm'
    apply (le_div_iff₀ (show (0:ℝ) < 2 by norm_num)).mpr
    simpa only [mul_comm] using hl.le
  change U ((t : Plane)*Complex.I) ≤ (B+ε)*t
  apply hpoint.trans
  change (S*Real.sqrt E.area+K*t)*t ≤ (B+ε)*t
  apply mul_le_mul_of_nonneg_right _ ht.le
  calc
    S*Real.sqrt E.area+K*t ≤ (B+ε/2)+ε/2 := add_le_add hspec htK
    _ = B+ε := by ring

end Torsion

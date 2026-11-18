module

public import Torsion.Proof.PaperBoundarySequence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section

/-! # Attainment of the maximum quotient at a fixed supporting frame -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace Torsion.MaximizingNormalSequence

variable {T : DirichletTheory} {D : ConvexDomain}

/-- The one-frame rectangle comparison applied to the actual sample depths. -/
def RectangleComparison (s : MaximizingNormalSequence T D) : Prop :=
  ∀ (j : ℕ) (R δ η : ℝ), 0 < R → 0 < δ → 0 < η → η ≤ (T.G D).toReal →
    (∀ b : ℝ, |b| ≤ δ * R →
      s.value (s.points j + R • s.normals j + b • (-Complex.I * s.normals j)) ≤
        ((T.G D).toReal - η) * R) →
    s.depths j < R →
    s.value (s.points j + s.depths j • s.normals j) / s.depths j ≤
      (T.G D).toReal - η / Real.cosh (Real.pi / (2 * δ)) + R / 2

private theorem ray_quotient_le (s : MaximizingNormalSequence T D) {R : ℝ} (hR : 0 < R) :
    s.value (s.point + R • s.normal) / R ≤ (T.G D).toReal := by
  have hf := s.point_mem
  rw [D.isOpen.frontier_eq] at hf
  have h := s.lipschitz.dist_le_mul (s.point + R • s.normal) s.point
  rw [Real.dist_eq, s.zero_off _ hf.2, sub_zero, abs_of_nonneg (s.nonneg _),
    dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR,
    s.unit, mul_one] at h
  exact (div_le_iff₀ hR).mpr h

/-- A fixed linear deficit on the limiting normal transfers by continuity
to the centers of the sample rectangles, and by the Lipschitz estimate to
their roofs. The rectangle comparison propagates this deficit back to the
near-maximal quotients, contradicting their defining limit. -/
theorem fixed_normal_quotient (s : MaximizingNormalSequence T D)
    (hb : s.RectangleComparison) :
    Tendsto (fun t : ℝ => s.value (s.point + t • s.normal) / t) (𝓝[>] 0)
      (𝓝 (T.G D).toReal) := by
  let G := (T.G D).toReal
  have hG : 0 < G := T.G_toReal_pos D
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let η : ℝ := min ((G - a) / 4) (G / 4)
    have hη : 0 < η := lt_min (by change 0 < (G - a) / 4; linarith) (by positivity)
    have hηa : η ≤ (G - a) / 4 := min_le_left _ _
    have hηG : η ≤ G := (min_le_right _ _).trans (by linarith)
    let δ := η / G
    have hδ : 0 < δ := div_pos hη hG
    have hwidth : G * δ = η := by dsimp [δ]; field_simp
    let gap := η / Real.cosh (Real.pi / (2 * δ))
    have hgap : 0 < gap := div_pos hη (Real.cosh_pos _)
    have hsmall : ∀ᶠ R : ℝ in 𝓝[>] 0, R < gap :=
      (eventually_lt_nhds hgap).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with R hR0 hRsmall
    have hR : 0 < R := hR0
    by_contra! hfail
    have hcenter : s.value (s.point + R • s.normal) ≤ a * R :=
      (div_le_iff₀ hR).mp hfail
    have htarget : s.value (s.point + R • s.normal) < (G - 2 * η) * R := by
      apply hcenter.trans_lt
      apply mul_lt_mul_of_pos_right _ hR
      linarith
    have hc : Tendsto (fun j => s.value (s.points j + R • s.normals j)) atTop
        (𝓝 (s.value (s.point + R • s.normal))) :=
      (s.continuous.tendsto _).comp (s.points_tendsto.add (s.normals_tendsto.const_smul R))
    have hseq : ∀ᶠ j in atTop, s.value (s.points j + s.depths j • s.normals j) / s.depths j
        ≤ G - gap + R / 2 := by
      filter_upwards [hc.eventually_lt_const htarget, s.depths_tendsto.eventually_lt_const hR]
        with j hj htj
      apply hb j R δ η hR hδ hη hηG _ htj
      intro b hbr
      let c := s.points j + R • s.normals j
      let w := b • (-Complex.I * s.normals j)
      have hl := s.lipschitz.dist_le_mul (c + w) c
      have hd : dist (c + w) c = |b| := by
        rw [dist_eq_norm, add_sub_cancel_left]
        simp [w, s.sample_unit j]
      rw [Real.dist_eq, hd] at hl
      have hdiff := (le_abs_self (s.value (c + w) - s.value c)).trans hl
      change s.value (c + w) ≤ (G - η) * R
      change s.value c < (G - 2 * η) * R at hj
      have hbound : G * |b| ≤ η * R := by
        calc
          G * |b| ≤ G * (δ * R) := mul_le_mul_of_nonneg_left hbr hG.le
          _ = η * R := by rw [← mul_assoc, hwidth]
      change s.value (c + w) - s.value c ≤ G * |b| at hdiff
      linarith
    have hh : G ≤ G - gap + R / 2 :=
      le_of_tendsto_of_tendsto s.quotients_tendsto tendsto_const_nhds hseq
    linarith
  · intro b hb'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (s.ray_quotient_le ht).trans_lt hb'

/-- Positivity of the limiting slope forces eventual entry of the same
fixed normal ray into the original open convex domain. -/
theorem fixed_normal_enters (s : MaximizingNormalSequence T D) (hb : s.RectangleComparison) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, s.point + t • s.normal ∈ D.carrier := by
  have hp := (s.fixed_normal_quotient hb).eventually (lt_mem_nhds (T.G_toReal_pos D))
  filter_upwards [hp] with t ht
  by_contra hout
  rw [s.zero_off _ hout, zero_div] at ht
  exact (lt_irrefl _ ht)

end Torsion.MaximizingNormalSequence

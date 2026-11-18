module

public import Torsion.Proof.PaperBoundaryQuotients
public import Torsion.Proof.PaperGradientPositive
public import Mathlib.Topology.Sequences

@[expose] public section

/-! # Convergent supporting frames with near-maximal original-domain quotients -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion

/-- Genuine nearest-boundary samples of one continuous weak torsion solution. -/
structure MaximizingNormalSequence (T : DirichletTheory) (D : ConvexDomain) where
  value : Plane → ℝ
  weak : IsWeakTorsion D.carrier value (T.solution D).weakGradient
  value_eq : (T.solution D).value =ᵐ[volume.restrict D.carrier] value
  gradient_eq : (T.solution D).weakGradient =ᵐ[volume.restrict D.carrier] gradient value
  continuous : Continuous value
  smooth : ContDiffOn ℝ ∞ value D.carrier
  lipschitz : LipschitzWith (T.G D).toNNReal value
  zero_off : ∀ x ∉ D.carrier, value x = 0
  nonneg : ∀ x, 0 ≤ value x
  point : Plane
  normal : Plane
  point_mem : point ∈ frontier D.carrier
  unit : ‖normal‖ = 1
  support : ∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) normal (z - point)
  points : ℕ → Plane
  normals : ℕ → Plane
  depths : ℕ → ℝ
  points_tendsto : Tendsto points atTop (𝓝 point)
  normals_tendsto : Tendsto normals atTop (𝓝 normal)
  depths_tendsto : Tendsto depths atTop (𝓝 0)
  depth_pos : ∀ j, 0 < depths j
  sample_frontier : ∀ j, points j ∈ frontier D.carrier
  sample_unit : ∀ j, ‖normals j‖ = 1
  sample_support : ∀ j, ∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) (normals j) (z - points j)
  sample_inside : ∀ j, points j + depths j • normals j ∈ D.carrier
  sample_distance : ∀ j, infDist (points j + depths j • normals j) D.carrierᶜ = depths j
  quotients_tendsto :
    Tendsto (fun j => value (points j + depths j • normals j) / depths j)
      atTop (𝓝 (T.G D).toReal)

private theorem strict_support_of_nonnegative {D : ConvexDomain} {p n : Plane}
    (hn : ‖n‖ = 1) (h : ∀ z ∈ D.carrier, 0 ≤ inner (𝕜 := ℝ) n (z - p))
    (x : Plane) (hx : x ∈ D.carrier) : 0 < inner (𝕜 := ℝ) n (x - p) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp D.isOpen x hx
  let y := x - (r / 2) • n
  have hy : y ∈ ball x r := by
    rw [mem_ball, dist_eq_norm]
    have hid : y - x = -((r / 2) • n) := by dsimp [y]; abel
    rw [hid, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hr), hn, mul_one]
    linarith
  have hb := h y (hball hy)
  have hid : y - p = (x - p) - (r / 2) • n := by dsimp [y]; abel
  rw [hid, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn] at hb
  nlinarith

/-- Compactness can be applied to the observation frames while keeping the
original domain and torsion function fixed throughout the sequence. -/
theorem DirichletTheory.exists_maximizingNormalSequence (T : DirichletTheory)
    (D : ConvexDomain) : Nonempty (MaximizingNormalSequence T D) := by
  classical
  obtain ⟨U, hc, hs, hz, hp, hrep, hg, hLip, hobs⟩ := T.exists_near_maximal_normal_quotients D
  let G := (T.G D).toReal
  have hG : 0 < G := T.G_toReal_pos D
  let δ (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hδ (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  have hδone (k : ℕ) : δ k ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    simp
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let L (k : ℕ) : ℝ≥0 := ⟨G * (1 - δ k), mul_nonneg hG.le (sub_nonneg.mpr (hδone k))⟩
  have hL (k : ℕ) : (L k : ℝ≥0∞) < T.G D := by
    calc
      (L k : ℝ≥0∞) = ENNReal.ofReal (L k : ℝ) := ENNReal.ofReal_coe_nnreal.symm
      _ < ENNReal.ofReal G := (ENNReal.ofReal_lt_ofReal_iff hG).mpr (by
        change G * (1 - δ k) < G
        nlinarith [mul_pos hG (hδ k)])
      _ = T.G D := ENNReal.ofReal_toReal (T.G_lt_top D).ne
  choose p n t hfront hn hsup ht htδ hinside hdist hlo hhi using
    fun k => hobs (δ k) (hδ k) (L k) (hL k)
  have htlim : Tendsto t atTop (𝓝 0) :=
    squeeze_zero (fun k => (ht k).le) (fun k => (htδ k).le) hδlim
  have hloLim : Tendsto (fun k => (L k : ℝ)) atTop (𝓝 G) := by
    change Tendsto (fun k => G * (1 - δ k)) atTop (𝓝 G)
    simpa only [sub_zero, mul_one] using (hδlim.const_sub 1).const_mul G
  have hqLim := tendsto_of_tendsto_of_tendsto_of_le_of_le hloLim tendsto_const_nhds
    (fun k => (hlo k).le) hhi
  have hcp := (D.bounded.isCompact_closure.of_isClosed_subset isClosed_frontier
    frontier_subset_closure).prod (isCompact_sphere (0 : Plane) 1)
  obtain ⟨b, hb, σ, hσ, hlim⟩ := hcp.tendsto_subseq (x := fun k => (p k, n k))
    (fun k => ⟨hfront k, by simpa only [mem_sphere, dist_zero_right] using hn k⟩)
  change Tendsto (fun j => (p (σ j), n (σ j))) atTop (𝓝 b) at hlim
  have hunit : ‖b.2‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hb.2
  have hplim : Tendsto (fun k => p (σ k)) atTop (𝓝 b.1) := hlim.fst_nhds
  have hnlim : Tendsto (fun k => n (σ k)) atTop (𝓝 b.2) := hlim.snd_nhds
  have hsup' (z : Plane) (hzD : z ∈ D.carrier) : 0 ≤ inner (𝕜 := ℝ) b.2 (z - b.1) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (hnlim.inner (hplim.const_sub z))
      (Eventually.of_forall (fun k => (hsup (σ k) z hzD).le))
  exact ⟨{
    value := U, weak := (T.solution D).weakEquation.of_zero_extension_representative
      D.isOpen.measurableSet hrep hz,
    value_eq := hrep, gradient_eq := hg, continuous := hc, smooth := hs, lipschitz := hLip,
    zero_off := hz, nonneg := hp, point := b.1, normal := b.2, unit := hunit,
    point_mem := hb.1, support := strict_support_of_nonnegative hunit hsup',
    points := p ∘ σ, normals := n ∘ σ, depths := t ∘ σ,
    points_tendsto := hplim, normals_tendsto := hnlim, depths_tendsto := htlim.comp hσ.tendsto_atTop,
    depth_pos := fun j => ht (σ j), sample_frontier := fun j => hfront (σ j),
    sample_unit := fun j => hn (σ j), sample_support := fun j => hsup (σ j),
    sample_inside := fun j => hinside (σ j), sample_distance := fun j => hdist (σ j),
    quotients_tendsto := hqLim.comp hσ.tendsto_atTop }⟩

end Torsion

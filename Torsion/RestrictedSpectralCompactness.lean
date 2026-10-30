module

public import Torsion.RestrictedSpectralFourierBounds
public import Torsion.RestrictedSpectralFourierWindows
public import Torsion.RestrictedSpectralGraphHilbert
public import Mathlib.Analysis.Normed.Operator.Compact

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual compactness of the restricted half-energy inclusion

Uniform Fourier bounds and a common frequency Lipschitz modulus give
compact cutoff families by Arzelà--Ascoli. The actual half-energy makes
the discarded Fourier L² tails uniformly small. Genuine Parseval then
transfers total boundedness to the actual value L² classes. In particular
the value inclusion from the constructed restricted Hilbert graph is compact.
-/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace Torsion.Spectral

/-- The actual norm of the discarded frequency window is exactly its
actual Fourier L² tail. -/
theorem norm_sub_frequencyWindow_sq_eq_tail {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (R : ℝ) :
    ‖hf.toLp f - frequencyWindow R (hf.toLp f)‖ ^ 2 =
      ∫ ξ in {ξ : ℝ | R < |ξ|}, ‖f ξ‖ ^ 2 := by
  let u := hf.toLp f
  have hnorm := integral_norm_sq_eq_norm_toLp_sq
    (Lp.memLp (u - frequencyWindow R u))
  rw [Lp.toLp_coeFn] at hnorm
  rw [← hnorm]
  have hS : MeasurableSet {ξ : ℝ | R < |ξ|} :=
    isOpen_lt continuous_const continuous_abs |>.measurableSet
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u (frequencyWindow R u), hf.coeFn_toLp,
    frequencyWindow_ae R u] with ξ hsub hξ hwindow
  dsimp only [Pi.sub_apply] at hsub
  rw [hsub, hwindow]
  by_cases hI : ξ ∈ Icc (-R) R
  · have hnot : ξ ∉ {ξ : ℝ | R < |ξ|} := not_lt_of_ge (abs_le.2 hI)
    simp only [indicator_of_mem hI, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      indicator_of_notMem hnot]
  · have htail : ξ ∈ {ξ : ℝ | R < |ξ|} := lt_of_not_ge (fun h => hI (abs_le.1 h))
    simp only [indicator_of_notMem hI, sub_zero, indicator_of_mem htail]
    dsimp only [u] at hξ ⊢
    rw [hξ]

/-- Uniform approximation by totally bounded families gives total
boundedness in the actual ambient metric space. -/
theorem totallyBounded_range_of_uniform_approximations
    {ι E : Type*} [PseudoMetricSpace E] (F : ι → E)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ G : ι → E,
      TotallyBounded (range G) ∧ ∀ i, dist (F i) (G i) ≤ ε / 2) :
    TotallyBounded (range F) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨G, hG, happ⟩ := happrox ε hε
  obtain ⟨T, hTfin, hcover⟩ := Metric.totallyBounded_iff.mp hG (ε / 2) (half_pos hε)
  refine ⟨T, hTfin, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨z, hzT, hz⟩ := Set.mem_iUnion₂.mp (hcover (mem_range_self i))
  apply Set.mem_iUnion₂.mpr
  refine ⟨z, hzT, ?_⟩
  change dist (F i) z < ε
  have hz' : dist (G i) z < ε / 2 := hz
  have ht := dist_triangle (F i) (G i) z
  linarith [happ i]

/-- A nonexpansive relation between two indexed families transfers total
boundedness, without requiring injectivity of the indexing map. -/
theorem totallyBounded_range_of_dist_le
    {ι E F : Type*} [MetricSpace E] [MetricSpace F] (V : ι → E) (W : ι → F)
    (hdist : ∀ i j, dist (V i) (V j) ≤ dist (W i) (W j))
    (hW : TotallyBounded (range W)) : TotallyBounded (range V) := by
  classical
  let pick : range W → ι := fun x => Classical.choose x.property
  have hpick (x : range W) : W (pick x) = (x : F) := Classical.choose_spec x.property
  let G : range W → E := fun x => V (pick x)
  have hLip : LipschitzWith 1 G := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (V (pick x)) (V (pick y)) ≤ (1 : ℝ) * dist (x : F) (y : F)
    simpa only [one_mul, hpick] using hdist (pick x) (pick y)
  have hTB : TotallyBounded (univ : Set (range W)) := by
    apply (totallyBounded_preimage
      (isUniformEmbedding_subtype_val (p := fun x : F => x ∈ range W)).isUniformInducing hW).subset
    intro x _
    exact x.property
  apply (hTB.image hLip.uniformContinuous).subset
  rintro _ ⟨i, rfl⟩
  let x : range W := ⟨W i, mem_range_self i⟩
  refine ⟨x, mem_univ _, ?_⟩
  have h := hdist (pick x) i
  rw [hpick] at h
  have hx : (x : F) = W i := rfl
  rw [hx, dist_self] at h
  exact dist_eq_zero.mp (le_antisymm h dist_nonneg)

/-- Every family bounded in the actual value norm and actual half-energy
has a totally bounded family of genuine Fourier L² classes. -/
theorem totallyBounded_restricted_fourier_family {ι : Type*}
    (f : ι → ℝ → ℝ) (hf : ∀ i, MemRestrictedFormDomain (f i))
    (M C : ℝ≥0) (hM : ∀ i, ‖(hf i).1.toLp (f i)‖ ≤ (M : ℝ))
    (hC : ∀ i, energy (f i) (f i) ≤ (C : ℝ)) :
    TotallyBounded (range (fun i => (hf i).fourier_parseval.1.toLp (fourier (f i)))) := by
  let F : ι → Lp ℂ 2 (volume : Measure ℝ) :=
    fun i => (hf i).fourier_parseval.1.toLp (fourier (f i))
  have hbound (i : ι) (ξ : ℝ) : ‖fourier (f i) ξ‖ ≤ ((2 * M : ℝ≥0) : ℝ) := by
    have h := (hf i).norm_fourier_le_two_norm ξ
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using h.trans (by nlinarith [hM i])
  have hLip (i : ι) : LipschitzWith (4 * M) (fourier (f i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro ξ η
    rw [dist_eq_norm, Real.dist_eq]
    have h := (hf i).norm_fourier_sub_le ξ η
    have hm := mul_le_mul_of_nonneg_right (hM i) (abs_nonneg (ξ - η))
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using h.trans (by nlinarith)
  apply totallyBounded_range_of_uniform_approximations F
  intro ε hε
  let R : ℝ := 1 + (8 * Real.pi * (C : ℝ)) / ε ^ 2
  have hR : 0 < R := by dsimp only [R]; positivity
  have hRscale : 8 * Real.pi * (C : ℝ) ≤ ε ^ 2 * R := by
    have hh : ε ^ 2 * ((8 * Real.pi * (C : ℝ)) / ε ^ 2) = 8 * Real.pi * (C : ℝ) := by
      field_simp [hε.ne']
    dsimp only [R]
    nlinarith [sq_nonneg ε]
  have hsmall : (2 * Real.pi / R) * (C : ℝ) ≤ (ε / 2) ^ 2 := by
    have hh : (2 * Real.pi * (C : ℝ)) / R ≤ (ε / 2) ^ 2 := by
      apply (div_le_iff₀ hR).mpr
      convert mul_le_mul_of_nonneg_left hRscale (show (0 : ℝ) ≤ 1 / 4 by norm_num) using 1 <;> ring
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  refine ⟨fun i => frequencyWindow R (F i), ?_, ?_⟩
  · exact (isCompact_closure_range_frequencyWindow hR (fun i => fourier (f i))
      (fun i => (hf i).fourier_parseval.1) (2 * M) (4 * M) hbound hLip).totallyBounded.subset subset_closure
  · intro i
    rw [dist_eq_norm]
    apply (sq_le_sq₀ (norm_nonneg _) (half_pos hε).le).mp
    calc
      _ = ∫ ξ in {ξ : ℝ | R < |ξ|}, ‖fourier (f i) ξ‖ ^ 2 :=
        norm_sub_frequencyWindow_sq_eq_tail (hf i).fourier_parseval.1 R
      _ ≤ (2 * Real.pi / R) * energy (f i) (f i) :=
        fourier_tail_integral_le (hf i).integrable (hf i).2.1 hR
      _ ≤ (2 * Real.pi / R) * (C : ℝ) :=
        mul_le_mul_of_nonneg_left (hC i) (by positivity)
      _ ≤ _ := hsmall

/-- Parseval identifies the actual Fourier and value distances, and hence
the value family inherits genuine compactness from its frequency family. -/
theorem totallyBounded_restricted_value_family {ι : Type*}
    (f : ι → ℝ → ℝ) (hf : ∀ i, MemRestrictedFormDomain (f i))
    (M C : ℝ≥0) (hM : ∀ i, ‖(hf i).1.toLp (f i)‖ ≤ (M : ℝ))
    (hC : ∀ i, energy (f i) (f i) ≤ (C : ℝ)) :
    TotallyBounded (range (fun i => (hf i).1.toLp (f i))) := by
  let V : ι → Lp ℝ 2 (volume : Measure ℝ) := fun i => (hf i).1.toLp (f i)
  let F : ι → Lp ℂ 2 (volume : Measure ℝ) :=
    fun i => (hf i).fourier_parseval.1.toLp (fourier (f i))
  apply totallyBounded_range_of_dist_le V F ?_ (totallyBounded_restricted_fourier_family f hf M C hM hC)
  intro i j
  have hsub : MemRestrictedFormDomain (fun x => f i x - f j x) := by
    simpa only [sub_eq_add_neg, neg_one_mul] using (hf i).add ((hf j).const_mul (-1))
  have hP := hsub.fourier_parseval.2
  rw [fourier_sub (hf i).integrable (hf j).integrable] at hP
  simp only [Pi.sub_apply] at hP
  have hfreq : (∫ ξ : ℝ, ‖fourier (f i) ξ - fourier (f j) ξ‖ ^ 2) = ‖F i - F j‖ ^ 2 := by
    simpa only [MemLp.toLp_sub, Pi.sub_apply, F] using
      integral_norm_sq_eq_norm_toLp_sq ((hf i).fourier_parseval.1.sub (hf j).fourier_parseval.1)
  have hval : (∫ x : ℝ, (f i x - f j x) ^ 2) = ‖V i - V j‖ ^ 2 := by
    simpa only [MemLp.toLp_sub, Pi.sub_apply, V] using
      integral_sq_eq_norm_toLp_sq ((hf i).1.sub (hf j).1)
  rw [hfreq, hval] at hP
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hpi : 1 ≤ 2 * Real.pi := by have h := Real.two_le_pi; linarith
  nlinarith [mul_le_mul_of_nonneg_right hpi (sq_nonneg ‖V i - V j‖)]

namespace RestrictedHilbert

/-- The genuine value inclusion of the actual restricted Hilbert graph is
compact. Every approximation and norm identity used here has been proved
over the original concrete restricted Fourier definitions. -/
theorem valueMap_isCompactOperator : IsCompactOperator (valueMap : space → ValueL2) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall valueMap.toLinearMap
    (show (0 : ℝ) < 1 by norm_num)).mpr
  let I := Metric.closedBall (0 : space) 1
  let f : I → ℝ → ℝ := fun p => valueMap (p : space)
  have hf (p : I) : MemRestrictedFormDomain (f p) := memRestrictedFormDomain_coordinates p.1
  have hp (p : I) : ‖(p : space)‖ ≤ 1 := by
    simpa only [I, mem_closedBall, dist_zero_right] using p.property
  have hM (p : I) : ‖(hf p).1.toLp (f p)‖ ≤ (1 : ℝ≥0) := by
    have hv : ‖valueMap p.1‖ ≤ ‖p.1‖ := by
      have hh := norm_sq p.1
      nlinarith [sq_nonneg ‖halfMap p.1‖, norm_nonneg (valueMap p.1), norm_nonneg p.1]
    simpa only [f, Lp.toLp_coeFn] using hv.trans (hp p)
  let C : ℝ≥0 := ⟨1 / (2 * Real.pi), by positivity⟩
  have hC (p : I) : Torsion.Spectral.energy (f p) (f p) ≤ (C : ℝ) := by
    have hh := (half_norm_le p.1).trans (hp p)
    have hh2 : ‖halfMap p.1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (halfMap p.1)]
    have he : Torsion.Spectral.energy (f p) (f p) =
        (1 / (2 * Real.pi)) * ‖halfMap p.1‖ ^ 2 := by
      rw [← energy_eq_original p.1 p.1, energy_apply, real_inner_self_eq_norm_sq]
    rw [he]
    simpa only [C, mul_one] using mul_le_mul_of_nonneg_left hh2
      (show (0 : ℝ) ≤ 1 / (2 * Real.pi) by positivity)
  have hTB := totallyBounded_restricted_value_family f hf 1 C hM hC
  have hRange : range (fun p : I => (hf p).1.toLp (f p)) =
      valueMap '' Metric.closedBall (0 : space) 1 := by
    ext v
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨p.1, p.2, ?_⟩
      simp only [f, Lp.toLp_coeFn]
    · rintro ⟨p, hp, rfl⟩
      refine ⟨⟨p, hp⟩, ?_⟩
      simp only [f, Lp.toLp_coeFn]
  rw [hRange] at hTB
  exact isCompact_of_totallyBounded_isClosed hTB.closure isClosed_closure

end RestrictedHilbert
end Torsion.Spectral

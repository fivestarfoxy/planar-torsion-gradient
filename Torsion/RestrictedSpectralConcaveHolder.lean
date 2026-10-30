import Torsion.RestrictedSpectralHeightRegularity
import Torsion.RestrictedSpectralConcavityBounds
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Deriv

/-!
# Square-root modulus from actual concavity and endpoint bounds

The downward secants of a concave profile are bounded using its chord to
the zero endpoint. An actual square-root endpoint bound therefore gives
a square-root bound on all downward increments. Together with the
origin's linear bound, this yields a global one-half Hölder modulus after
odd reflection and zero extension.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion.Spectral

/-- Nonnegative concavity alone already gives a uniform interior bound.
No energy, differentiability, or endpoint hypothesis is required. -/
theorem concaveOn_nonneg_le_two_midpoint {f : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) f)
    (hnonneg : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ f x) :
    ∀ x ∈ Ioo (0 : ℝ) 1, f x ≤ 2 * f (1 / 2) := by
  intro x hx
  have hy : 1 - x ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hmid := hconc.2 hx hy (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hmid
  rw [show (1 / 2 : ℝ) * x + 1 / 2 * (1 - x) = 1 / 2 from by ring] at hmid
  nlinarith [hnonneg (1 - x) hy]

/-- Scalar cancellation used to convert an endpoint chord bound into a
square-root increment bound. -/
theorem mul_sqrt_le_mul_sqrt_of_le {h d : ℝ} (hh : 0 ≤ h) (hhd : h ≤ d) :
    h * Real.sqrt d ≤ d * Real.sqrt h := by
  have hd := hh.trans hhd
  have hs := Real.sqrt_le_sqrt hhd
  calc
    h * Real.sqrt d = Real.sqrt h * (Real.sqrt h * Real.sqrt d) := by rw [← mul_assoc, Real.mul_self_sqrt hh]
    _ ≤ Real.sqrt d * (Real.sqrt h * Real.sqrt d) :=
      mul_le_mul_of_nonneg_right hs (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = (Real.sqrt d * Real.sqrt d) * Real.sqrt h := by ring
    _ = d * Real.sqrt h := by rw [Real.mul_self_sqrt hd]

/-- A genuine square-root endpoint bound controls every falling secant
of a concave profile, including increments ending at the endpoint. -/
theorem concaveOn_sub_le_sqrt_of_endpoint_bound {f : ℝ → ℝ} {C x y : ℝ}
    (hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) f) (hfone : f 1 = 0) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ C * Real.sqrt (1 - t))
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x ≤ y) :
    f x - f y ≤ C * Real.sqrt (y - x) := by
  rcases eq_or_lt_of_le hxy with heq | hlt
  · subst y
    simp
  by_cases hy1 : y = 1
  · subst y
    simpa only [hfone, sub_zero] using hbound x hx
  have hylt : y < 1 := lt_of_le_of_ne hy.2 hy1
  have hsl := hconc.slope_anti_adjacent hx (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) hlt hylt
  rw [hfone, zero_sub] at hsl
  have hcross := (div_le_div_iff₀ (sub_pos.2 hylt) (sub_pos.2 hlt)).1 hsl
  have hchord : (f x - f y) * (1 - x) ≤ f x * (y - x) := by nlinarith
  have hxlt : x < 1 := hlt.trans hylt
  have hdiff : 0 ≤ y - x := sub_nonneg.2 hxy
  have hdiffle : y - x ≤ 1 - x := by linarith [hy.2]
  have hsqrt := mul_sqrt_le_mul_sqrt_of_le hdiff hdiffle
  have hmul := mul_le_mul_of_nonneg_left hsqrt hC
  have hfx := mul_le_mul_of_nonneg_right (hbound x hx) hdiff
  apply (mul_le_mul_right (sub_pos.2 hxlt)).1
  nlinarith [hchord, hfx, hmul]

/-- Explicit origin and endpoint bounds together control every positive-
half increment of a concave zero-endpoint profile. -/
theorem concaveOn_abs_sub_le_sqrt_of_bounds {f : ℝ → ℝ} {L C : ℝ}
    (hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) f) (hfzero : f 0 = 0) (hfone : f 1 = 0)
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hlinear : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ L * t)
    (hendpoint : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ C * Real.sqrt (1 - t)) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |f x - f y| ≤ (L + C) * Real.sqrt |x - y| := by
  have hordered (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
      (hxy : x ≤ y) : |f x - f y| ≤ (L + C) * Real.sqrt (y - x) := by
    have hdiff : 0 ≤ y - x := sub_nonneg.2 hxy
    have hdiff1 : y - x ≤ 1 := by linarith [hx.1, hy.2]
    have hhsqrt : y - x ≤ Real.sqrt (y - x) :=
      Real.le_sqrt_of_sq_le (by nlinarith)
    have hrise := concaveOn_sub_le_mul_sub_of_le_mul hconc hfzero hlinear hx hy hxy
    have hfall := concaveOn_sub_le_sqrt_of_endpoint_bound hconc hfone hC hendpoint hx hy hxy
    have hLmul := mul_le_mul_of_nonneg_left hhsqrt hL
    apply abs_le.2
    constructor <;> nlinarith [Real.sqrt_nonneg (y - x)]
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · simpa only [abs_of_nonpos (sub_nonpos.2 hxy), neg_sub] using hordered x y hx hy hxy
  · simpa only [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hyx)] using hordered y x hy hx hyx

/-- Positive-half square-root control extends to the actual odd zero
extension with an explicit doubled constant. -/
theorem abs_sub_le_sqrt_of_odd_zero_exterior {f : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hodd : Function.Odd f)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → f x = 0)
    (hhalf : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |f x - f y| ≤ K * Real.sqrt |x - y|) (x y : ℝ) :
    |f x - f y| ≤ (2 * K) * Real.sqrt |x - y| := by
  have hf0 : f 0 = 0 := by have h := hodd 0; simp only [neg_zero] at h; linarith
  have hclamp (t : ℝ) (ht : 0 ≤ t) : f t = f (min t 1) := by
    by_cases ht1 : t ≤ 1
    · rw [min_eq_left ht1]
    · rw [min_eq_right (le_of_not_ge ht1), hzero t (by rw [abs_of_nonneg ht]; exact le_of_not_ge ht1),
        hzero 1 (by norm_num)]
  have hpos (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
      |f s - f t| ≤ K * Real.sqrt |s - t| := by
    rw [hclamp s hs, hclamp t ht]
    have h := hhalf (min s 1) ⟨le_min hs (by norm_num), min_le_right _ _⟩
      (min t 1) ⟨le_min ht (by norm_num), min_le_right _ _⟩
    have hL : LipschitzWith 1 (fun z : ℝ => min z 1) := LipschitzWith.id.min_const 1
    have hdist : |min s 1 - min t 1| ≤ |s - t| := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hL.dist_le_mul s t
    exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdist) hK)
  have hpoint (s : ℝ) : |f s| ≤ K * Real.sqrt |s| := by
    by_cases hs : 0 ≤ s
    · simpa only [hf0, sub_zero] using hpos s 0 hs le_rfl
    · have h := hpos (-s) 0 (neg_nonneg.2 (le_of_not_ge hs)) le_rfl
      simpa only [hodd s, hf0, sub_zero, abs_neg] using h
  have hcross {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 0) :
      |f s - f t| ≤ (2 * K) * Real.sqrt |s - t| := by
    have hsa : |s| ≤ |s - t| := by rw [abs_of_nonneg hs, abs_of_nonneg (by linarith)]; linarith
    have hta : |t| ≤ |s - t| := by rw [abs_of_nonpos ht, abs_of_nonneg (by linarith)]; linarith
    calc
      |f s - f t| ≤ |f s| + |f t| := abs_sub _ _
      _ ≤ K * Real.sqrt |s| + K * Real.sqrt |t| := add_le_add (hpoint s) (hpoint t)
      _ ≤ K * Real.sqrt |s - t| + K * Real.sqrt |s - t| := add_le_add
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsa) hK)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hta) hK)
      _ = _ := by ring
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · exact (hpos x y hx hy).trans (by nlinarith [Real.sqrt_nonneg |x - y|])
    · exact hcross hx (le_of_not_ge hy)
  · by_cases hy : 0 ≤ y
    · simpa only [abs_sub_comm] using hcross hy (le_of_not_ge hx)
    · have h := hpos (-x) (-y) (neg_nonneg.2 (le_of_not_ge hx)) (neg_nonneg.2 (le_of_not_ge hy))
      simp only [hodd x, hodd y, neg_sub_neg, abs_sub_comm] at h
      exact h.trans (by nlinarith [Real.sqrt_nonneg |x - y|])

/-- The preceding concrete square-root modulus is genuine global
one-half Hölder continuity in mathlib's original metric definition. -/
theorem holder_half_of_odd_zero_exterior {f : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hodd : Function.Odd f)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → f x = 0)
    (hhalf : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |f x - f y| ≤ K * Real.sqrt |x - y|) :
    HolderWith ⟨2 * K, by positivity⟩ (1 / 2) f := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity)]
  rw [← ENNReal.ofReal_coe_nnreal]
  simp only [NNReal.coe_mk]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * K)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    ← Real.sqrt_eq_rpow] using abs_sub_le_sqrt_of_odd_zero_exterior hK hodd hzero hhalf x y


/-- Concavity together with concrete origin and endpoint estimates yields
genuine global Hölder one-half regularity for the odd zero extension. -/
theorem holder_half_of_concave_odd_zero_exterior {f : ℝ → ℝ} {L C : ℝ}
    (hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) f) (hodd : Function.Odd f)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → f x = 0) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hlinear : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ L * t)
    (hendpoint : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ C * Real.sqrt (1 - t)) :
    HolderWith ⟨2 * (L + C), by positivity⟩ (1 / 2) f := by
  have hfzero : f 0 = 0 := by have h := hodd 0; simp only [neg_zero] at h; linarith
  exact holder_half_of_odd_zero_exterior (add_nonneg hL hC) hodd hzero
    (concaveOn_abs_sub_le_sqrt_of_bounds hconc hfzero (hzero 1 (by norm_num)) hL hC hlinear hendpoint)

/-- The derivative at the smooth origin and a local right-endpoint
square-root bound suffice. The global estimates are constructed by
concavity and compactness, and the resulting exponent is exactly 1/2. -/
theorem exists_holder_half_of_concave_odd_local_endpoint_bound {f : ℝ → ℝ} {L K δ : ℝ}
    (hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) f) (hodd : Function.Odd f)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → f x = 0) (hL : 0 ≤ L) (hd : HasDerivAt f L 0)
    (hcont : ContinuousOn f (Ico (0 : ℝ) 1)) (hδ : 0 < δ)
    (hendpoint : ∀ t ∈ Icc (0 : ℝ) 1, 1 - δ < t → f t ≤ K * Real.sqrt (1 - t)) :
    ∃ C : ℝ≥0, HolderWith C (1 / 2) f := by
  have hfzero : f 0 = 0 := by have h := hodd 0; simp only [neg_zero] at h; linarith
  obtain ⟨C, hC, hCb⟩ := exists_global_sqrt_bound_of_local_endpoint_bound hcont hδ hendpoint
  exact ⟨⟨2 * (L + C), by positivity⟩, holder_half_of_concave_odd_zero_exterior
    hconc hodd hzero hL hC (concaveOn_le_mul_of_hasDerivAt hconc hfzero hd) hCb⟩


/-- A genuine derivative at the origin suffices; its nonnegative part
provides the rising-secant constant, so no derivative-sign assumption is
needed for this Hölder conclusion. -/
theorem exists_holder_half_of_concave_odd_differentiable_local_endpoint_bound
    {f : ℝ → ℝ} {K δ : ℝ}
    (hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) f) (hodd : Function.Odd f)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → f x = 0) (hd : DifferentiableAt ℝ f 0)
    (hcont : ContinuousOn f (Ico (0 : ℝ) 1)) (hδ : 0 < δ)
    (hendpoint : ∀ t ∈ Icc (0 : ℝ) 1, 1 - δ < t → f t ≤ K * Real.sqrt (1 - t)) :
    ∃ C : ℝ≥0, HolderWith C (1 / 2) f := by
  have hfzero : f 0 = 0 := by have h := hodd 0; simp only [neg_zero] at h; linarith
  obtain ⟨C, hC, hCb⟩ := exists_global_sqrt_bound_of_local_endpoint_bound hcont hδ hendpoint
  let L : ℝ := max (deriv f 0) 0
  have hL : 0 ≤ L := le_max_right _ _
  have hlinear : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ L * t := by
    intro t ht
    exact (concaveOn_le_mul_of_hasDerivAt hconc hfzero hd.hasDerivAt t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.1)
  exact ⟨⟨2 * (L + C), by positivity⟩,
    holder_half_of_concave_odd_zero_exterior hconc hodd hzero hL hC hlinear hCb⟩


/-- A genuine local square-root endpoint bound gives continuity at the
zero endpoint, independently of concavity or global Hölder regularity. -/
theorem continuousWithinAt_one_of_local_sqrt_endpoint_bound {f : ℝ → ℝ} {K δ : ℝ}
    (hfone : f 1 = 0) (hnonneg : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) (hδ : 0 < δ)
    (hendpoint : ∀ t ∈ Icc (0 : ℝ) 1, 1 - δ < t → f t ≤ K * Real.sqrt (1 - t)) :
    ContinuousWithinAt f (Icc (0 : ℝ) 1) 1 := by
  have hlim : Tendsto (fun t : ℝ => K * Real.sqrt (1 - t))
      (𝓝[Icc (0 : ℝ) 1] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => K * Real.sqrt (1 - t)) 1 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  change Tendsto f (𝓝[Icc (0 : ℝ) 1] 1) (𝓝 (f 1))
  rw [hfone]
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact hnonneg t ht
  · have hnear : ∀ᶠ t : ℝ in 𝓝[Icc (0 : ℝ) 1] 1, 1 - δ < t :=
      nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith))
    filter_upwards [self_mem_nhdsWithin, hnear] with t ht hnear
    exact hendpoint t ht hnear

/-- Continuity on the half-open interval and actual square-root decay at
its zero endpoint supply continuity on the full closed interval. -/
theorem continuousOn_Icc_of_local_sqrt_endpoint_bound {f : ℝ → ℝ} {K δ : ℝ}
    (hcont : ContinuousOn f (Ico (0 : ℝ) 1)) (hfone : f 1 = 0)
    (hnonneg : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) (hδ : 0 < δ)
    (hendpoint : ∀ t ∈ Icc (0 : ℝ) 1, 1 - δ < t → f t ≤ K * Real.sqrt (1 - t)) :
    ContinuousOn f (Icc (0 : ℝ) 1) := by
  intro x hx
  by_cases hx1 : x = 1
  · subst x
    exact continuousWithinAt_one_of_local_sqrt_endpoint_bound hfone hnonneg hδ hendpoint
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hIco : Ico (0 : ℝ) 1 ∈ 𝓝[Icc (0 : ℝ) 1] x := by
      apply mem_nhdsWithin_iff_exists_mem_nhds_inter.2
      exact ⟨Iio 1, Iio_mem_nhds hxlt, by intro y hy; exact ⟨hy.2.1, hy.1⟩⟩
    exact (hcont x ⟨hx.1, hxlt⟩).mono_of_mem_nhdsWithin hIco


/-- Interior concavity, the actual zero extension, smoothness at the
origin, and an independent local square-root endpoint estimate suffice
for global one-half Hölder continuity. Endpoint continuity and closed-
interval concavity are proved along the way. -/
theorem exists_holder_half_of_concaveOn_Ioo_odd_local_endpoint_bound
    {f : ℝ → ℝ} {K δ : ℝ}
    (hconc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) f) (hodd : Function.Odd f)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → f x = 0)
    (hnonneg : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ f x) (hd : DifferentiableAt ℝ f 0)
    (hcont : ContinuousOn f (Ico (0 : ℝ) 1)) (hδ : 0 < δ)
    (hendpoint : ∀ t ∈ Icc (0 : ℝ) 1, 1 - δ < t → f t ≤ K * Real.sqrt (1 - t)) :
    ∃ C : ℝ≥0, HolderWith C (1 / 2) f := by
  have hfzero : f 0 = 0 := by have h := hodd 0; simp only [neg_zero] at h; linarith
  have hfone : f 1 = 0 := hzero 1 (by norm_num)
  have hnonnegIcc : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x := by
    intro x hx
    by_cases hx0 : x = 0
    · simp only [hx0, hfzero, le_refl]
    by_cases hx1 : x = 1
    · simp only [hx1, hfone, le_refl]
    exact hnonneg x ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
  have hclosed := continuousOn_Icc_of_local_sqrt_endpoint_bound hcont hfone hnonnegIcc hδ hendpoint
  have hconcClosed := concaveOn_Icc_of_concaveOn_Ioo_of_continuousOn (by norm_num : (0 : ℝ) < 1)
    hconc hclosed
  exact exists_holder_half_of_concave_odd_differentiable_local_endpoint_bound
    hconcClosed hodd hzero hd hcont hδ hendpoint

/-- This form applies directly to the actual analytic interior spectral
representative once its concavity and endpoint estimate are proved. -/
theorem exists_holder_half_of_analytic_concave_odd_local_endpoint_bound
    {f : ℝ → ℝ} {K δ : ℝ}
    (ha : AnalyticOnNhd ℝ f (Ioo (-1 : ℝ) 1))
    (hconc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) f) (hodd : Function.Odd f)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → f x = 0)
    (hnonneg : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ f x) (hδ : 0 < δ)
    (hendpoint : ∀ t ∈ Icc (0 : ℝ) 1, 1 - δ < t → f t ≤ K * Real.sqrt (1 - t)) :
    ∃ C : ℝ≥0, HolderWith C (1 / 2) f := by
  apply exists_holder_half_of_concaveOn_Ioo_odd_local_endpoint_bound
    hconc hodd hzero hnonneg (ha 0 (by constructor <;> norm_num)).differentiableAt ?_ hδ hendpoint
  intro x hx
  exact (ha x ⟨by linarith [hx.1], hx.2⟩).continuousAt.continuousWithinAt

end Torsion.Spectral

module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Concrete secant and endpoint bounds for concave interval profiles

These ordinary real-variable estimates turn a local linear bound at zero
into a global one, bound all rising secants, and patch a local endpoint
square-root estimate using continuity only away from that endpoint.
-/

noncomputable section
open Set

namespace Torsion.Spectral

/-- A global linear upper bound at the zero endpoint controls every
rising secant of a concave profile. -/
theorem concaveOn_sub_le_mul_sub_of_le_mul {f : ℝ → ℝ} {L x y : ℝ}
    (hf : ConcaveOn ℝ (Icc (0 : ℝ) 1) f) (hzero : f 0 = 0)
    (hbound : ∀ z ∈ Icc (0 : ℝ) 1, f z ≤ L * z)
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x ≤ y) :
    f y - f x ≤ L * (y - x) := by
  by_cases heq : x = y
  · subst y
    simp
  have hlt : x < y := lt_of_le_of_ne hxy heq
  by_cases hx0 : x = 0
  · subst x
    simpa only [hzero, sub_zero] using hbound y hy
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hslope := hf.slope_anti_adjacent (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    hy hxpos hlt
  simp only [hzero, sub_zero] at hslope
  have hL : f x / x ≤ L := (div_le_iff₀ hxpos).2 (hbound x hx)
  exact (div_le_iff₀ (sub_pos.2 hlt)).1 (hslope.trans hL)

/-- A genuine derivative at the zero endpoint supplies a global linear
upper bound for the concave profile. -/
theorem concaveOn_le_mul_of_hasDerivAt {f : ℝ → ℝ} {L : ℝ}
    (hf : ConcaveOn ℝ (Icc (0 : ℝ) 1) f) (hzero : f 0 = 0)
    (hd : HasDerivAt f L 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ L * x := by
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0, hzero]
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hs := hf.slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) hx hxpos hd
  rw [slope_def_field, hzero, sub_zero, sub_zero] at hs
  exact (div_le_iff₀ hxpos).1 hs

/-- A merely local linear upper estimate at zero already extends to the
whole concave interval. -/
theorem concaveOn_le_mul_of_local_bound {f : ℝ → ℝ} {L δ : ℝ}
    (hf : ConcaveOn ℝ (Icc (0 : ℝ) 1) f) (hzero : f 0 = 0) (hδ : 0 < δ)
    (hlocal : ∀ z ∈ Icc (0 : ℝ) 1, z < δ → f z ≤ L * z) :
    ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ L * x := by
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0, hzero]
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  let z : ℝ := min (x / 2) (δ / 2)
  have hzpos : 0 < z := lt_min (by positivity) (by positivity)
  have hzx : z < x := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hzδ : z < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hz : z ∈ Icc (0 : ℝ) 1 := ⟨hzpos.le, hzx.le.trans hx.2⟩
  have hlocalz := hlocal z hz hzδ
  have hslope := hf.slope_anti_adjacent
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) hx hzpos hzx
  simp only [hzero, sub_zero] at hslope
  have hL : f z / z ≤ L := (div_le_iff₀ hzpos).2 hlocalz
  have hsec := (div_le_iff₀ (sub_pos.2 hzx)).1 (hslope.trans hL)
  nlinarith

/-- A local endpoint square-root estimate and continuity on compact
interior intervals produce one global square-root bound. No continuity
at the right endpoint is needed. -/
theorem exists_global_sqrt_bound_of_local_endpoint_bound {f : ℝ → ℝ} {K δ : ℝ}
    (hf : ContinuousOn f (Ico (0 : ℝ) 1)) (hδ0 : 0 < δ)
    (hlocal : ∀ x ∈ Icc (0 : ℝ) 1, 1 - δ < x → f x ≤ K * Real.sqrt (1 - x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ C * Real.sqrt (1 - x) := by
  have hsub : Icc (0 : ℝ) (1 - δ) ⊆ Ico (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, hx.2.trans_lt (by linarith)⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image (hf.mono hsub)
  let C : ℝ := max 0 (max K (max M 0 / Real.sqrt δ))
  have hC : 0 ≤ C := le_max_left _ _
  have hK : K ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hratio : max M 0 / Real.sqrt δ ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hsqrtδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  refine ⟨C, hC, ?_⟩
  intro x hx
  by_cases hnear : 1 - δ < x
  · exact (hlocal x hx hnear).trans
      (mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg _))
  · have hxinterior : x ∈ Icc (0 : ℝ) (1 - δ) := ⟨hx.1, le_of_not_gt hnear⟩
    have hfx : f x ≤ M := hM (mem_image_of_mem f hxinterior)
    have hmC : max M 0 ≤ C * Real.sqrt δ := (div_le_iff₀ hsqrtδ).1 hratio
    have hsqrt : Real.sqrt δ ≤ Real.sqrt (1 - x) := Real.sqrt_le_sqrt (by linarith)
    exact hfx.trans ((le_max_left M 0).trans
      (hmC.trans (mul_le_mul_of_nonneg_left hsqrt hC)))

/-- Concavity on an open interval extends to its closed interval whenever
the actual endpoint values give a continuous extension. Jensen's two
continuous sides agree with the interior inequality on a dense product. -/
theorem concaveOn_Icc_of_concaveOn_Ioo_of_continuousOn
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ConcaveOn ℝ (Ioo a b) f) (hc : ContinuousOn f (Icc a b)) :
    ConcaveOn ℝ (Icc a b) f := by
  refine ⟨convex_Icc a b, ?_⟩
  intro x hx y hy c d hc0 hd0 hcd
  have hclosure : closure (Ioo a b ×ˢ Ioo a b) = Icc a b ×ˢ Icc a b := by
    rw [closure_prod_eq, closure_Ioo hab.ne]
  have hfst : ContinuousOn (fun p : ℝ × ℝ => f p.1) (Icc a b ×ˢ Icc a b) :=
    hc.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hsnd : ContinuousOn (fun p : ℝ × ℝ => f p.2) (Icc a b ×ˢ Icc a b) :=
    hc.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hleft : ContinuousOn (fun p : ℝ × ℝ => c * f p.1 + d * f p.2)
      (closure (Ioo a b ×ˢ Ioo a b)) := by
    rw [hclosure]
    exact (continuousOn_const.mul hfst).add (continuousOn_const.mul hsnd)
  have hright : ContinuousOn (fun p : ℝ × ℝ => f (c * p.1 + d * p.2))
      (closure (Ioo a b ×ˢ Ioo a b)) := by
    rw [hclosure]
    apply hc.comp ((continuous_const.mul continuous_fst).add
      (continuous_const.mul continuous_snd)).continuousOn
    intro p hp
    simpa only [smul_eq_mul, Pi.add_apply, Pi.mul_apply] using (convex_Icc a b) hp.1 hp.2 hc0 hd0 hcd
  have hJ : ∀ p ∈ Ioo a b ×ˢ Ioo a b,
      c * f p.1 + d * f p.2 ≤ f (c * p.1 + d * p.2) := by
    intro p hp
    simpa only [smul_eq_mul] using hf.2 hp.1 hp.2 hc0 hd0 hcd
  have hxy : (x, y) ∈ closure (Ioo a b ×ˢ Ioo a b) := by
    rw [hclosure]
    exact ⟨hx, hy⟩
  simpa only [smul_eq_mul] using le_on_closure hJ hleft hright hxy

end Torsion.Spectral

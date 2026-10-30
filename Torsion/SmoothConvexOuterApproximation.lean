import Torsion.ConvexMollification
import Torsion.ConvexOuterApproximation
import Torsion.SmoothConvexLevelSets
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth strongly convex outer approximation of concrete planar domains

The construction mollifies the actual Minkowski gauge and adds a small
positive squared Euclidean norm. Its sublevel is a genuine outer domain,
and the defining function is smooth and strongly convex. All metric
containments are quantitative consequences of the gauge estimates.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Pointwise Topology ENNReal NNReal ContDiff

namespace Torsion

theorem convexOn_gauge_of_convex {D : Set Plane} (hD : Convex ℝ D)
    (habs : Absorbent ℝ D) : ConvexOn ℝ univ (gauge D) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  calc
    gauge D (a • x + b • y) ≤ gauge D (a • x) + gauge D (b • y) :=
      gauge_add_le hD habs _ _
    _ = a • gauge D x + b • gauge D y := by
      rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb]

/-- Every centered convex domain has a smooth strongly convex defining
function whose strict sublevel contains the domain and lies in any
prescribed metric thickening. This constructs both the domain and function. -/
theorem ConvexDomain.exists_smooth_stronglyConvex_outer_centered
    (D : ConvexDomain) (hzero : (0 : Plane) ∈ D.carrier)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (E : ConvexDomain) (F : Plane → ℝ) (c μ : ℝ),
      ContDiff ℝ ∞ F ∧ StrongConvexOn univ μ F ∧ 0 < μ ∧ F 0 < c ∧
      E.carrier = {x | F x < c} ∧ D.carrier ⊆ E.carrier ∧
      E.carrier ⊆ thickening δ D.carrier := by
  have hnhds : D.carrier ∈ 𝓝 (0 : Plane) := D.isOpen.mem_nhds hzero
  have habs : Absorbent ℝ D.carrier := absorbent_nhds_zero hnhds
  obtain ⟨K, hK⟩ := D.convex.lipschitz_gauge hnhds
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.mp D.bounded
  let R : ℝ := max R₀ 1
  have hR : 1 ≤ R := le_max_right _ _
  have hnorm : ∀ x ∈ D.carrier, ‖x‖ ≤ R :=
    fun x hx => (hR₀ x hx).trans (le_max_left _ _)
  let t : ℝ := δ / (12 * (R + 1))
  have ht : 0 < t := div_pos hδ (by positivity)
  let η : ℝ := t / (R ^ 2 + 1)
  have hη : 0 < η := div_pos ht (by positivity)
  obtain ⟨g, hgs, hgc, happrox⟩ := exists_contDiff_convex_uniform_approximation
    (convexOn_gauge_of_convex D.convex habs) hK ht
  let F : Plane → ℝ := fun x => g x + η * ‖x‖ ^ 2
  let c : ℝ := 1 + 2 * t
  let s : ℝ := 1 + 3 * t
  have hs : 0 < s := by dsimp [s]; positivity
  have hFs : ContDiff ℝ ∞ F := hgs.add (contDiff_const.mul (contDiff_norm_sq ℝ))
  have hFc : StrongConvexOn univ (2 * η) F := by
    rw [strongConvexOn_iff_convex]
    convert hgc using 1
    funext x
    dsimp [F]
    ring
  have hFzero : F 0 < c := by
    have hg0 := (abs_le.mp (happrox 0)).2
    simp only [gauge_zero, sub_zero] at hg0
    dsimp [F, c]
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] using
      (show g 0 < 1 + 2 * t by linarith)
  have hDE : D.carrier ⊆ {x | F x < c} := by
    intro x hx
    have hgauge : gauge D.carrier x < 1 := gauge_lt_one_of_mem_of_isOpen D.isOpen hx
    have hg := (abs_le.mp (happrox x)).2
    have hxnorm : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [hnorm x hx, norm_nonneg x]
    have hηR : η * R ^ 2 < t := by
      dsimp [η]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by positivity : 0 < R ^ 2 + 1)).mpr
      nlinarith
    change F x < c
    dsimp [F, c]
    nlinarith [mul_le_mul_of_nonneg_left hxnorm hη.le]
  have hEsD : {x | F x < c} ⊆ s • D.carrier := by
    intro x hx
    have hlo := (abs_le.mp (happrox x)).1
    have hgauge : gauge D.carrier x < s := by
      have hnonneg : 0 ≤ η * ‖x‖ ^ 2 := mul_nonneg hη.le (sq_nonneg _)
      change g x + η * ‖x‖ ^ 2 < 1 + 2 * t at hx
      dsimp [s]
      linarith
    have hmem : s⁻¹ • x ∈ D.carrier := by
      rw [← gauge_lt_one_eq_self_of_isOpen D.convex hzero D.isOpen]
      change gauge D.carrier (s⁻¹ • x) < 1
      rw [gauge_smul_of_nonneg (inv_nonneg.mpr hs.le), smul_eq_mul]
      exact (inv_mul_lt_iff₀ hs).mpr (by simpa using hgauge)
    exact ⟨s⁻¹ • x, hmem, smul_inv_smul₀ hs.ne' x⟩
  let E : ConvexDomain :=
    { carrier := {x | F x < c}
      isOpen := isOpen_lt hFs.continuous continuous_const
      bounded := (D.bounded.smul₀ s).subset hEsD
      convex := by simpa using (hFc.strictConvexOn (by positivity)).convexOn.convex_lt c
      nonempty := D.nonempty.mono hDE }
  refine ⟨E, F, c, 2 * η, hFs, hFc, by positivity, hFzero, rfl, hDE, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hEsD hx
  apply mem_thickening_iff.mpr
  refine ⟨y, hy, ?_⟩
  have htr : 3 * t * R < δ := by
    dsimp [t]
    have hden : 0 < 12 * (R + 1) := by positivity
    have he : 3 * (δ / (12 * (R + 1))) * R = (3 * δ * R) / (12 * (R + 1)) := by ring
    rw [he]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  calc
    dist (s • y) y = (3 * t) * ‖y‖ := by
      have he : s • y - y = (3 * t) • y := by
        change (1 + 3 * t) • y - y = (3 * t) • y
        rw [add_smul, one_smul]
        abel
      rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 3 * t)]
    _ ≤ 3 * t * R := mul_le_mul_of_nonneg_left (hnorm y hy) (by positivity)
    _ < δ := htr

/-- Every original convex domain admits actual smooth strictly convex outer
domains arbitrarily close in the metric sense. Smoothness is supplied by an
explicit globally smooth defining function with nonzero derivative on the
entire actual frontier; strict convexity includes its closure. -/
theorem ConvexDomain.exists_smooth_strictConvex_outer
    (D : ConvexDomain) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (E : ConvexDomain) (F : Plane → ℝ) (c : ℝ),
      ContDiff ℝ ∞ F ∧ StrictConvexOn ℝ univ F ∧
      StrictConvex ℝ (closure E.carrier) ∧
      (∀ x ∈ frontier E.carrier, fderiv ℝ F x ≠ 0) ∧
      E.carrier = {x | F x < c} ∧ D.carrier ⊆ E.carrier ∧
      E.carrier ⊆ thickening δ D.carrier := by
  obtain ⟨a, ha⟩ := D.nonempty
  let D₀ := D.translate (-a)
  have hzero : (0 : Plane) ∈ D₀.carrier := by simpa [D₀] using ha
  obtain ⟨E₀, F₀, c, μ, hFs, hFc, hμ, hFzero, hE₀, hDE₀, hED₀⟩ :=
    D₀.exists_smooth_stronglyConvex_outer_centered hzero hδ
  let E := E₀.translate a
  let F : Plane → ℝ := fun x => F₀ (x - a)
  have hFs' : ContDiff ℝ ∞ F := hFs.comp (contDiff_id.sub contDiff_const)
  have hFc' : StrictConvexOn ℝ univ F := by
    simpa only [preimage_univ, Function.comp_def, ← sub_eq_add_neg] using
      (hFc.strictConvexOn hμ).translate_left (-a)
  have hE : E.carrier = {x | F x < c} := by
    change (fun z : Plane => z - a) ⁻¹' E₀.carrier = _
    rw [hE₀]
    rfl
  have hFbelow : ∃ y, F y < c := ⟨a, by simpa [F] using hFzero⟩
  refine ⟨E, F, c, hFs', hFc', ?_, ?_, hE, ?_, ?_⟩
  · rw [hE]
    exact strictConvex_closure_sublevel hFs'.continuous hFc' c
  · intro x hx
    apply fderiv_ne_zero_of_convex_level hFc'.convexOn
      (hFs'.differentiable (by simp)) hFbelow
    rw [hE] at hx
    exact sublevel_eq_of_mem_frontier hFs'.continuous hx
  · intro x hx
    change x - a ∈ E₀.carrier
    apply hDE₀
    simpa [D₀] using hx
  · intro x hx
    change x - a ∈ E₀.carrier at hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp (hED₀ hx)
    apply mem_thickening_iff.mpr
    refine ⟨y + a, ?_, ?_⟩
    · simpa [D₀] using hy
    · have hdist : dist x (y + a) = dist (x - a) y := by
        simpa only [sub_add_cancel] using dist_add_right (x - a) y a
      rw [hdist]
      exact hxy

end Torsion

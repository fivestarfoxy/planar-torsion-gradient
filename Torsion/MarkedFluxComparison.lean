import Torsion.DomainComparison
import Torsion.DilationWeak
import Torsion.BoundaryLowerBound
import Torsion.RadialFluxConcavity.Transfer

/-!
# Marked flux laws from the actual weak PDE

The relation below requires a continuous representative in a half-ball and
the finite marked quotient limit. It does not assert existence of that
representative or limit. Once they exist, positivity, uniqueness, domain
comparison, supermodularity and scaling follow from the proved weak PDE.
In particular those laws are not separate assumptions about a flux function.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Pointwise

namespace Torsion

/-- A genuine weak torsion solution with a continuous marked representative
and a finite inward quotient limit. Only local continuity is required. -/
def HasTorsionFlux (D : Set Plane) (q : ℝ) : Prop :=
  ∃ (u : Plane → ℝ) (g : Plane → Plane) (r : ℝ),
    IsWeakTorsion D u g ∧ 0 < r ∧
    ContinuousOn u (upperHalfPlane ∩ Metric.ball 0 r) ∧ HasMarkedFlux u q

private theorem halfBall_isOpen (r : ℝ) :
    IsOpen (upperHalfPlane ∩ Metric.ball (0 : Plane) r) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball

/-- The inward vertical ray eventually belongs to every positive half-ball. -/
theorem eventually_vertical_mem_halfBall {r : ℝ} (hr : 0 < r) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (t : ℂ) * Complex.I ∈ upperHalfPlane ∩ Metric.ball 0 r := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htr
  have ht' : 0 < t := ht
  refine ⟨?_, ?_⟩
  · simpa [upperHalfPlane] using ht
  · simpa [Metric.mem_ball, dist_zero_right, norm_mul, abs_of_pos ht'] using htr

/-- Almost-everywhere scalar order becomes pointwise order for continuous
representatives on an open set of positive Lebesgue measure. -/
theorem leOn_open_of_ae_le {U : Set Plane} {u v : Plane → ℝ}
    (hU : IsOpen U) (hu : ContinuousOn u U) (hv : ContinuousOn v U)
    (hle : ∀ᵐ x ∂volume, u x ≤ v x) : ∀ x ∈ U, u x ≤ v x := by
  have heq : (fun x => max (u x) (v x)) =ᵐ[volume.restrict U] v := by
    filter_upwards [ae_restrict_of_ae hle] with x hx
    exact max_eq_right hx
  have hp := Measure.eqOn_open_of_ae_eq heq hU (hu.sup hv) hv
  intro x hx
  exact max_eq_right_iff.mp (hp hx)

/-- A.e. order of locally continuous marked representatives passes to their
actual inward quotient limits. Null exceptional sets cannot be sampled on
the ray directly; local continuity supplies this missing step. -/
theorem HasMarkedFlux.le_of_ae_le {u v : Plane → ℝ} {q p r s : ℝ}
    (hq : HasMarkedFlux u q) (hp : HasMarkedFlux v p)
    (hr : 0 < r) (hs : 0 < s)
    (hu : ContinuousOn u (upperHalfPlane ∩ Metric.ball 0 r))
    (hv : ContinuousOn v (upperHalfPlane ∩ Metric.ball 0 s))
    (hle : ∀ᵐ x ∂volume, u x ≤ v x) : q ≤ p := by
  let a := min r s
  have ha : 0 < a := lt_min hr hs
  have hsubr : upperHalfPlane ∩ Metric.ball (0 : Plane) a ⊆
      upperHalfPlane ∩ Metric.ball 0 r :=
    inter_subset_inter_right _ (Metric.ball_subset_ball (min_le_left _ _))
  have hsubs : upperHalfPlane ∩ Metric.ball (0 : Plane) a ⊆
      upperHalfPlane ∩ Metric.ball 0 s :=
    inter_subset_inter_right _ (Metric.ball_subset_ball (min_le_right _ _))
  have hpoint := leOn_open_of_ae_le (halfBall_isOpen a)
    (hu.mono hsubr) (hv.mono hsubs) hle
  apply le_of_tendsto_of_tendsto hq hp
  filter_upwards [eventually_vertical_mem_halfBall ha, self_mem_nhdsWithin] with t ht ht0
  exact div_le_div_of_nonneg_right (hpoint _ ht) ht0.le

/-- Marked torsion flux is nonnegative whenever the local continuous flux
representative exists. This follows from actual weak torsion positivity. -/
theorem HasTorsionFlux.nonneg {D : Set Plane} {q : ℝ}
    (hq : HasTorsionFlux D q) (hb : Bornology.IsBounded D) : 0 ≤ q := by
  obtain ⟨u, g, r, hu, hr, hc, hf⟩ := hq
  have hz : HasMarkedFlux (fun _ : Plane => (0 : ℝ)) 0 := by
    simp [HasMarkedFlux]
  exact hz.le_of_ae_le hf hr hr continuousOn_const hc (hu.nonneg_ae hb)

/-- Inclusion monotonicity of the genuine flux relation, deduced from the
weak comparison theorem rather than assumed as an independent flux law. -/
theorem HasTorsionFlux.mono {D E : Set Plane} {q p : ℝ}
    (hq : HasTorsionFlux D q) (hp : HasTorsionFlux E p)
    (hD : IsOpen D) (hE : IsOpen E)
    (hbD : Bornology.IsBounded D) (hbE : Bornology.IsBounded E) (hDE : D ⊆ E) :
    q ≤ p := by
  obtain ⟨u, g, r, hu, hr, hc, hf⟩ := hq
  obtain ⟨v, h, s, hv, hs, hvc, hvf⟩ := hp
  exact hf.le_of_ae_le hvf hr hs hc hvc (hu.mono hv hD hE hbD hbE hDE)

/-- The marked flux is independent of all weak-solution and representative
choices once continuity near the marked point is required. -/
theorem HasTorsionFlux.unique {D : Set Plane} {q p : ℝ}
    (hq : HasTorsionFlux D q) (hp : HasTorsionFlux D p)
    (hD : IsOpen D) (hb : Bornology.IsBounded D) : q = p :=
  le_antisymm (hq.mono hp hD hD hb hb Subset.rfl)
    (hp.mono hq hD hD hb hb Subset.rfl)

/-- A differentiable local representative vanishing at the marked point
constructs the genuine flux. The original weak solution may be any a.e.
representative: it is changed only on a null set in the marked half-ball. -/
theorem HasTorsionFlux.of_localRepresentative {D : Set Plane}
    {u v : Plane → ℝ} {g : Plane → Plane} {r : ℝ}
    (hu : IsWeakTorsion D u g) (hr : 0 < r)
    (hv : ContinuousOn v (upperHalfPlane ∩ Metric.ball 0 r))
    (hae : u =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 r)] v)
    (hv0 : v 0 = 0) (hvd : DifferentiableAt ℝ v 0) :
    HasTorsionFlux D (gradient v 0).im := by
  classical
  let U : Set Plane := upperHalfPlane ∩ Metric.ball 0 r
  let w : Plane → ℝ := fun x => if x ∈ U then v x else u x
  have huw : u =ᵐ[volume] w := by
    filter_upwards [ae_imp_of_ae_restrict hae] with x hx
    by_cases hU : x ∈ U
    · simpa only [w, if_pos hU] using hx hU
    · simp only [w, if_neg hU]
  have hweak : IsWeakTorsion D w g :=
    ⟨hu.1.congr huw EventuallyEq.rfl, hu.2⟩
  have hcont : ContinuousOn w U := by
    apply hv.congr
    intro x hx
    simp only [w, U, if_pos hx]
  have hline : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const Complex.I
  have hdv : HasFDerivAt v (fderiv ℝ v 0) ((0 : ℂ) * Complex.I) := by
    simpa using hvd.hasFDerivAt
  have hd : HasDerivAt (fun t : ℝ => v ((t : ℂ) * Complex.I)) (gradient v 0).im 0 := by
    convert hdv.comp_hasDerivAt 0 hline using 1
    simp [fderiv_apply_eq_inner_gradient, Complex.inner, Complex.mul_re]
  have hf := hasMarkedFlux_of_normal_derivative hv0 hd
  refine ⟨w, g, r, hweak, hr, hcont, ?_⟩
  apply hf.congr'
  filter_upwards [eventually_vertical_mem_halfBall hr] with t ht
  simp only [w, U, if_pos ht]

/-- Additivity of finite quotient limits. -/
theorem HasMarkedFlux.add {u v : Plane → ℝ} {q p : ℝ}
    (hq : HasMarkedFlux u q) (hp : HasMarkedFlux v p) :
    HasMarkedFlux (fun x => u x + v x) (q + p) := by
  simpa only [HasMarkedFlux, add_div] using Filter.Tendsto.add hq hp

private theorem continuousOn_halfBall_add {u v : Plane → ℝ} {r s : ℝ}
    (hu : ContinuousOn u (upperHalfPlane ∩ Metric.ball 0 r))
    (hv : ContinuousOn v (upperHalfPlane ∩ Metric.ball 0 s)) :
    ContinuousOn (fun x => u x + v x)
      (upperHalfPlane ∩ Metric.ball 0 (min r s)) :=
  (hu.mono (inter_subset_inter_right _
    (Metric.ball_subset_ball (min_le_left _ _)))).add
  (hv.mono (inter_subset_inter_right _
    (Metric.ball_subset_ball (min_le_right _ _))))

/-- Supermodularity of genuine marked torsion flux follows from the proved
Sobolev intersection argument and weak PDE comparison. -/
theorem HasTorsionFlux.supermodular {D E : Set Plane} {qD qE qU qJ : ℝ}
    (hDq : HasTorsionFlux D qD) (hEq : HasTorsionFlux E qE)
    (hUq : HasTorsionFlux (D ∪ E) qU) (hJq : HasTorsionFlux (D ∩ E) qJ)
    (hD : IsOpen D) (hE : IsOpen E)
    (hbD : Bornology.IsBounded D) (hbE : Bornology.IsBounded E) :
    qD + qE ≤ qU + qJ := by
  obtain ⟨uD, gD, rD, huD, hrD, hcD, hfD⟩ := hDq
  obtain ⟨uE, gE, rE, huE, hrE, hcE, hfE⟩ := hEq
  obtain ⟨uU, gU, rU, huU, hrU, hcU, hfU⟩ := hUq
  obtain ⟨uJ, gJ, rJ, huJ, hrJ, hcJ, hfJ⟩ := hJq
  exact (hfD.add hfE).le_of_ae_le (hfU.add hfJ)
    (lt_min hrD hrE) (lt_min hrU hrJ)
    (continuousOn_halfBall_add hcD hcE) (continuousOn_halfBall_add hcU hcJ)
    (huD.supermodular huE huU huJ hD hE hbD hbE)

/-- The finite marked quotient limit has the physical degree-one scaling
under the already proved degree-two scaling of the torsion value. -/
theorem HasMarkedFlux.dilate {u : Plane → ℝ} {q : ℝ}
    (hq : HasMarkedFlux u q) (s : ℝ) (hs : 0 < s) :
    HasMarkedFlux (scaledValue s u) (s * q) := by
  have ht : Tendsto (fun t : ℝ => s⁻¹ * t) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using
        ((show Continuous (fun t : ℝ => s⁻¹ * t) from
          continuous_const.mul continuous_id).tendsto (0 : ℝ)).mono_left
          nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos (inv_pos.2 hs) ht
  have hlim := (hq.comp ht).const_mul s
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht0
  have ht0' : t ≠ 0 := ne_of_gt ht0
  symm
  change s ^ 2 * u (s⁻¹ • ((t : ℂ) * Complex.I)) / t =
    s * (u (((s⁻¹ * t : ℝ) : ℂ) * Complex.I) / (s⁻¹ * t))
  have heq : s⁻¹ • ((t : ℂ) * Complex.I) =
      ((s⁻¹ * t : ℝ) : ℂ) * Complex.I := by
    simp only [Complex.real_smul, Complex.ofReal_mul, mul_assoc]
  rw [heq]
  field_simp [hs.ne', ht0']
  ring

private theorem inverseDilation_mem_halfBall {s r : ℝ} (hs : 0 < s)
    {z : Plane} (hz : z ∈ upperHalfPlane ∩ Metric.ball 0 (s * r)) :
    s⁻¹ • z ∈ upperHalfPlane ∩ Metric.ball 0 r := by
  have him : 0 < z.im := hz.1
  have hn : ‖z‖ < s * r := by simpa [Metric.mem_ball, dist_zero_right] using hz.2
  refine ⟨?_, ?_⟩
  · simpa [upperHalfPlane, Complex.real_smul] using mul_pos (inv_pos.2 hs) him
  · have hlt := mul_lt_mul_of_pos_left hn (inv_pos.2 hs)
    have heq : s⁻¹ * (s * r) = r := by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    rw [heq] at hlt
    simpa [Metric.mem_ball, dist_zero_right, norm_smul, abs_of_pos hs] using hlt

/-- Actual weak PDE scaling and local representative transport construct the
scaled flux; neither a flux homogeneity law nor uniqueness is assumed. -/
theorem HasTorsionFlux.dilate {D : Set Plane} {q : ℝ}
    (hq : HasTorsionFlux D q) (s : ℝ) (hs : 0 < s) :
    HasTorsionFlux (s • D) (s * q) := by
  obtain ⟨u, g, r, hu, hr, hc, hf⟩ := hq
  refine ⟨scaledValue s u, scaledGradient s g, s * r,
    hu.dilate s hs, mul_pos hs hr, ?_, hf.dilate s hs⟩
  exact continuousOn_const.mul (hc.comp
    (show Continuous (fun z : Plane => s⁻¹ • z) from
      continuous_const.smul continuous_id).continuousOn
    (fun z hz => inverseDilation_mem_halfBall hs hz))

/-- Marked domains are closed under union. -/
theorem IsMarked.union {D E : Set Plane} (hD : IsMarked D) (hE : IsMarked E) :
    IsMarked (D ∪ E) := by
  obtain ⟨hDo, hDb, hDH, r, hr, hDr⟩ := hD
  obtain ⟨hEo, hEb, hEH, s, hs, hEs⟩ := hE
  refine ⟨hDo.union hEo, hDb.union hEb, union_subset hDH hEH,
    min r s, lt_min hr hs, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hb⟩
    exact ⟨(union_subset hDH hEH) hz, hb⟩
  · rintro ⟨hz, hb⟩
    have hbr : z ∈ Metric.ball (0 : Plane) r :=
      Metric.ball_subset_ball (min_le_left r s) hb
    have hzD : z ∈ D ∩ Metric.ball 0 r := by rw [hDr]; exact ⟨hz, hbr⟩
    exact ⟨Or.inl hzD.1, hb⟩

/-- Marked domains are closed under intersection, with a common smaller
flat half-ball. This includes domains with interface slits. -/
theorem IsMarked.inter {D E : Set Plane} (hD : IsMarked D) (hE : IsMarked E) :
    IsMarked (D ∩ E) := by
  obtain ⟨hDo, hDb, hDH, r, hr, hDr⟩ := hD
  obtain ⟨hEo, hEb, hEH, s, hs, hEs⟩ := hE
  refine ⟨hDo.inter hEo, hDb.subset inter_subset_left,
    inter_subset_left.trans hDH, min r s, lt_min hr hs, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hb⟩
    exact ⟨hDH hz.1, hb⟩
  · rintro ⟨hz, hb⟩
    have hbr : z ∈ Metric.ball (0 : Plane) r :=
      Metric.ball_subset_ball (min_le_left r s) hb
    have hbs : z ∈ Metric.ball (0 : Plane) s :=
      Metric.ball_subset_ball (min_le_right r s) hb
    have hzD : z ∈ D ∩ Metric.ball 0 r := by rw [hDr]; exact ⟨hz, hbr⟩
    have hzE : z ∈ E ∩ Metric.ball 0 s := by rw [hEs]; exact ⟨hz, hbs⟩
    exact ⟨⟨hzD.1, hzE.1⟩, hb⟩

/-- The physical positive dilation of a marked domain is marked. -/
theorem IsMarked.dilate {D : Set Plane} (hD : IsMarked D) (s : ℝ) (hs : 0 < s) :
    IsMarked (s • D) := by
  obtain ⟨hDo, hDb, hDH, r, hr, hDr⟩ := hD
  have hsub : s • D ⊆ upperHalfPlane := by
    rintro z ⟨w, hw, rfl⟩
    have hi : 0 < w.im := hDH hw
    simpa [upperHalfPlane, Complex.real_smul] using mul_pos hs hi
  refine ⟨hDo.smul₀ hs.ne', hDb.smul₀ s, hsub, s * r, mul_pos hs hr, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hb⟩
    exact ⟨hsub hz, hb⟩
  · intro hz
    have hback := inverseDilation_mem_halfBall hs hz
    have hw : s⁻¹ • z ∈ D ∩ Metric.ball 0 r := by rw [hDr]; exact hback
    refine ⟨⟨s⁻¹ • z, hw.1, ?_⟩, hz.2⟩
    simp [smul_smul, hs.ne']

/-- The one remaining local analytic input for the flux construction.
No comparison, scaling or supermodularity law is included in this input. -/
def MarkedFluxExistence : Prop :=
  ∀ (D : Set Plane), IsMarked D → ∃ q : ℝ, HasTorsionFlux D q

/-- The unique genuine marked flux, when local boundary regularity supplies
existence. Values on nonmarked sets are immaterial and set to zero. -/
def markedFlux (h : MarkedFluxExistence) (D : Set Plane) : ℝ := by
  classical
  exact if hD : IsMarked D then Classical.choose (h D hD) else 0

theorem markedFlux_spec (h : MarkedFluxExistence) {D : Set Plane} (hD : IsMarked D) :
    HasTorsionFlux D (markedFlux h D) := by
  classical
  simp only [markedFlux, dif_pos hD]
  exact Classical.choose_spec (h D hD)

/-- All three PDE laws used in radial concavity now follow from the actual
weak theory and the single local representative/finite-limit existence input.
They need not be assumed separately. -/
theorem markedFluxRules_of_exists (h : MarkedFluxExistence) :
    RadialFluxConcavity.MarkedFluxRules (markedFlux h) := by
  constructor
  · intro D E hD hE hDE
    exact (markedFlux_spec h hD).mono (markedFlux_spec h hE)
      hD.1 hE.1 hD.2.1 hE.2.1 hDE
  · intro D hD s hs
    have hS := hD.dilate s hs
    exact (markedFlux_spec h hS).unique ((markedFlux_spec h hD).dilate s hs)
      hS.1 hS.2.1
  · intro D E hD hE
    exact (markedFlux_spec h hD).supermodular (markedFlux_spec h hE)
      (markedFlux_spec h (hD.union hE)) (markedFlux_spec h (hD.inter hE))
      hD.1 hE.1 hD.2.1 hE.2.1

/-- Radial concavity for genuine weak torsion flux reduces to local marked
regularity, rather than to three independent assumed laws for a set function. -/
theorem markedFlux_radial_concaveOn (h : MarkedFluxExistence) :
    ConcaveOn ℝ RadialFluxConcavity.positiveContinuousProfiles
      (fun R => markedFlux h (radialDomain R)) :=
  RadialFluxConcavity.radial_flux_concaveOn (markedFluxRules_of_exists h)

end Torsion

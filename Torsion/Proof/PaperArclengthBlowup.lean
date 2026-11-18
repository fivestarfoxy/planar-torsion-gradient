module

public import Torsion.Proof.PaperBoundaryArclength
public import Torsion.Proof.PaperBoundaryBump
public import Torsion.Proof.PaperRadialFrameCoverage
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Tangent-line limit of arclength at a regular point

A compactly supported radial test sees exactly one half-line on the side
of a simple arc. Adding two half-arcs gives the full tangent-line density
at a simple closed curve, including its parameter seam.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Torsion.HermiteHadamard

/-- Speed-weighted pullback of a rescaled radial bump centered at p. -/
def arcBump (γ : ℝ → Plane) (β : ℝ → ℝ) (p : Plane) (ε t : ℝ) : ℝ :=
  β (‖γ t - p‖ / ε) * ‖deriv γ t‖

private theorem arcBump_continuous {γ : ℝ → Plane} (hγ : ContDiff ℝ 1 γ)
    {β : ℝ → ℝ} (hβ : Continuous β) (p : Plane) (ε : ℝ) :
    Continuous (arcBump γ β p ε) :=
  (hβ.comp ((hγ.continuous.sub continuous_const).norm.div_const ε)).mul hγ.continuous_deriv_one.norm

/-- At a regular endpoint, a non-returning compact arc has the rescaled
arclength of a half-line. The scalar test may have either sign. -/
theorem arcBump_right_limit {γ : ℝ → Plane} (hγ : ContDiff ℝ 1 γ) {a b : ℝ} (hab : a < b)
    (hreg : deriv γ a ≠ 0) (hunique : ∀ t ∈ Ioc a b, γ t ≠ γ a)
    {β : ℝ → ℝ} (hβ : Continuous β) {M : ℝ} (hM : 0 < M) (hcut : ∀ y, M ≤ y → β y = 0) :
    Tendsto (fun ε : ℝ => ε⁻¹ * ∫ t in a..b, arcBump γ β (γ a) ε t)
      (𝓝[>] 0) (𝓝 (∫ y in Ioi (0 : ℝ), β y)) := by
  let d (t : ℝ) := ‖dslope γ a t‖
  let v := ‖deriv γ a‖
  have hv : 0 < v := norm_pos_iff.mpr hreg
  have hd : Continuous d := continuous_iff_continuousAt.mpr fun t => by
    by_cases h : t = a
    · subst t
      exact (continuousAt_dslope_same.mpr (hγ.differentiable (by decide) a)).norm
    · exact ((continuousAt_dslope_of_ne h).mpr hγ.continuous.continuousAt).norm
  have hda : d a = v := by simp [d, v, dslope_same]
  have hpos (t : ℝ) (ht : t ∈ Icc a b) : 0 < d t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · simpa [← h, hda] using hv
    · apply norm_pos_iff.mpr
      intro hz
      have hs := sub_smul_dslope γ a t
      rw [hz, smul_zero] at hs
      exact hunique t ⟨h, ht.2⟩ (sub_eq_zero.mp hs.symm)
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hd.continuousOn
  let m := d t₀
  have hm : 0 < m := hpos _ ht₀
  have hlow (t) (ht : t ∈ Icc a b) : m ≤ d t := hmin ht
  let B := M/m
  have hB : 0 < B := div_pos hM hm
  have hBm : B*m = M := div_mul_cancel₀ _ hm.ne'
  have hBv : M ≤ B*v := by
    rw [← hBm]
    exact mul_le_mul_of_nonneg_left (hda ▸ hlow a ⟨le_rfl,hab.le⟩) hB.le
  let A (ε s : ℝ) := β (s * d (ε*s+a)) * ‖deriv γ (ε*s+a)‖
  have hA : Continuous A.uncurry := by
    have hc : Continuous (fun q : ℝ × ℝ => q.1*q.2+a) := (continuous_fst.mul continuous_snd).add continuous_const
    exact (hβ.comp (continuous_snd.mul (hd.comp hc))).mul (hγ.continuous_deriv_one.norm.comp hc)
  have hlim := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hA 0 B).continuousAt (x:=0)
  have htarget : (∫ s in 0..B, A 0 s) = ∫ y in Ioi (0 : ℝ), β y := by
    simp only [A, zero_mul, zero_add, hda]
    change (∫ s in 0..B, β (s*v) * v) = _
    rw [intervalIntegral.integral_mul_const, mul_comm _ v, ← smul_eq_mul,
      intervalIntegral.smul_integral_comp_mul_right, zero_mul,
      intervalIntegral.integral_of_le (mul_nonneg hB.le hv.le)]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun x hx => hx.1)
    intro y hy
    exact hcut y (hBv.trans (le_of_not_ge (fun h => hy.2 ⟨hy.1, h⟩)))
  rw [← htarget]
  apply (hlim.continuousWithinAt (s := Ioi 0)).tendsto.congr'
  have hδ : 0 < (b-a)/B := div_pos (sub_pos.mpr hab) hB
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hδ)] with ε hε hεB
  have he : 0 < ε := hε
  have hmid : ε*B+a ≤ b := by have := (lt_div_iff₀ hB).mp hεB; linarith
  have hn (t : ℝ) (ht : a ≤ t) : ‖γ t - γ a‖ = (t-a)*d t := by
    rw [← sub_smul_dslope γ a t, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht)]
  have htail : (∫ t in (ε*B+a)..b, arcBump γ β (γ a) ε t) = 0 := by
    rw [intervalIntegral.integral_of_le hmid]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    have hat : a ≤ t := by nlinarith [mul_pos he hB, ht.1]
    have hds := hlow t ⟨hat,ht.2⟩
    have hthreshold : M*ε ≤ (t-a)*d t := by
      calc
        _ = (ε*B)*m := by rw [mul_assoc, hBm, mul_comm]
        _ ≤ (t-a)*d t := mul_le_mul (by linarith [ht.1]) hds hm.le (sub_nonneg.mpr hat)
    simp [arcBump, hn t hat, hcut _ ((le_div_iff₀ he).mpr hthreshold)]
  have htrunc : (∫ t in a..b, arcBump γ β (γ a) ε t) =
      ∫ t in a..(ε*B+a), arcBump γ β (γ a) ε t := by
    have hc := arcBump_continuous hγ hβ (γ a) ε
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a (ε*B+a))
      (hc.intervalIntegrable _ b), htail, add_zero]
  rw [htrunc]
  have hsubst := intervalIntegral.integral_comp_mul_add (arcBump γ β (γ a) ε) (a:=0) (b:=B) he.ne' a
  simp only [mul_zero,zero_add,smul_eq_mul] at hsubst
  rw [← hsubst]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hB.le] at hs
  have hs' : a ≤ ε*s+a := le_add_of_nonneg_left (mul_nonneg he.le hs.1)
  simp only [A, arcBump, hn _ hs', add_sub_cancel_right]
  congr 2
  field_simp

/-- The corresponding half-line limit at the right endpoint of an arc. -/
theorem arcBump_left_limit {γ : ℝ → Plane} (hγ : ContDiff ℝ 1 γ) {a b : ℝ} (hab : a < b)
    (hreg : deriv γ b ≠ 0) (hunique : ∀ t ∈ Ico a b, γ t ≠ γ b)
    {β : ℝ → ℝ} (hβ : Continuous β) {M : ℝ} (hM : 0 < M) (hcut : ∀ y, M ≤ y → β y = 0) :
    Tendsto (fun ε : ℝ => ε⁻¹ * ∫ t in a..b, arcBump γ β (γ b) ε t)
      (𝓝[>] 0) (𝓝 (∫ y in Ioi (0 : ℝ), β y)) := by
  let g (t : ℝ) := γ (-t)
  have hg : ContDiff ℝ 1 g := hγ.comp contDiff_neg
  have hreg' : deriv g (-b) ≠ 0 := by simpa [g, deriv_comp_neg] using hreg
  have huniq (t) (ht : t ∈ Ioc (-b) (-a)) : g t ≠ g (-b) := by
    simpa [g] using hunique (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hr := arcBump_right_limit hg (neg_lt_neg hab) hreg' huniq hβ hM hcut
  apply hr.congr'
  apply Eventually.of_forall
  intro ε
  dsimp only
  apply congrArg ((ε⁻¹) * ·)
  have h := intervalIntegral.integral_comp_neg (arcBump γ β (γ b) ε) (a := -b) (b := -a)
  simpa only [g, arcBump, deriv_comp_neg, neg_neg, norm_neg] using h

private theorem arcBump_split {γ : ℝ → Plane} (hγ : ContDiff ℝ 1 γ)
    {β : ℝ → ℝ} (hβ : Continuous β) (p : Plane) {a t b : ℝ}
    (h₁ : Tendsto (fun ε : ℝ => ε⁻¹ * ∫ s in a..t, arcBump γ β p ε s)
      (𝓝[>] 0) (𝓝 (∫ y in Ioi (0 : ℝ), β y)))
    (h₂ : Tendsto (fun ε : ℝ => ε⁻¹ * ∫ s in t..b, arcBump γ β p ε s)
      (𝓝[>] 0) (𝓝 (∫ y in Ioi (0 : ℝ), β y))) :
    Tendsto (fun ε : ℝ => ε⁻¹ * ∫ s in a..b, arcBump γ β p ε s)
      (𝓝[>] 0) (𝓝 (∫ y : ℝ, β |y|)) := by
  rw [integral_comp_abs, two_mul]
  apply (h₁.add h₂).congr'
  apply Eventually.of_forall
  intro ε
  dsimp only [Pi.add_apply]
  have hc := arcBump_continuous hγ hβ p ε
  rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a t) (hc.intervalIntegrable t b)]

/-- A continuous radial test against the true arclength measure of a regular
simple closed curve converges, after rescaling about any boundary point,
to the integral of that test on a line. The endpoint parameters may have
different tangent vectors and are counted as two half-arcs. -/
theorem curveArclength_radial_blowup {γ : ℝ → Plane} (hγ : ContDiff ℝ 1 γ) {a b : ℝ}
    (hab : a < b) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (hreg : ∀ s ∈ Icc a b, deriv γ s ≠ 0) {t : ℝ} (ht : t ∈ Icc a b)
    {β : ℝ → ℝ} (hβ : Continuous β) {M : ℝ} (hM : 0 < M) (hcut : ∀ y, M ≤ y → β y = 0) :
    Tendsto (fun ε : ℝ => ε⁻¹ * ∫ z, β (‖z-γ t‖ / ε) ∂curveArclength γ a b)
      (𝓝[>] 0) (𝓝 (∫ y : ℝ, β |y|)) := by
  have hem : ∀ s ∈ Ioo a b, γ s ≠ γ a := fun s hs h =>
    hs.1.ne' (hinj ⟨hs.1.le,hs.2⟩ ⟨le_rfl,hab⟩ h)
  have hseam : Tendsto (fun ε : ℝ => ε⁻¹ * ∫ s in a..b, arcBump γ β (γ a) ε s)
      (𝓝[>] 0) (𝓝 (∫ y : ℝ, β |y|)) := by
    let m := (a+b)/2
    have ham : a < m := by dsimp [m]; linarith
    have hmb : m < b := by dsimp [m]; linarith
    apply arcBump_split hγ hβ (γ a) (t := m)
    · exact arcBump_right_limit hγ ham (hreg a ⟨le_rfl,hab.le⟩)
        (fun s hs => hem s ⟨hs.1,hs.2.trans_lt hmb⟩) hβ hM hcut
    · rw [hclosed]
      exact arcBump_left_limit hγ hmb (hreg b ⟨hab.le,le_rfl⟩)
        (fun s hs => hclosed ▸ hem s ⟨ham.trans_le hs.1,hs.2⟩) hβ hM hcut
  have hparam : Tendsto (fun ε : ℝ => ε⁻¹ * ∫ s in a..b, arcBump γ β (γ t) ε s)
      (𝓝[>] 0) (𝓝 (∫ y : ℝ, β |y|)) := by
    rcases eq_or_lt_of_le ht.1 with h | hat
    · simpa [← h] using hseam
    rcases eq_or_lt_of_le ht.2 with h | htb
    · simpa [h, ← hclosed] using hseam
    apply arcBump_split hγ hβ (γ t) (t := t)
    · exact arcBump_left_limit hγ hat (hreg t ht)
        (fun s hs h => hs.2.ne (hinj ⟨hs.1,hs.2.trans htb⟩ ⟨hat.le,htb⟩ h)) hβ hM hcut
    · apply arcBump_right_limit hγ htb (hreg t ht) _ hβ hM hcut
      intro s hs h
      rcases hs.2.eq_or_lt with he | hsb
      · subst s
        exact hem t ⟨hat,htb⟩ (h.symm.trans hclosed.symm)
      · exact hs.1.ne' (hinj ⟨hat.le.trans hs.1.le,hsb⟩ ⟨hat.le,htb⟩ h)
  apply hparam.congr'
  apply Eventually.of_forall
  intro ε
  dsimp only
  apply congrArg ((ε⁻¹) * ·)
  rw [integral_curveArclength hγ a b (f := fun z => β (‖z-γ t‖ / ε)) (hβ.comp ((continuous_id.sub continuous_const).norm.div_const ε)).measurable,
    intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  exact mul_comm _ _

/-- Two polar parameter values on a half-open full turn cannot represent
the same boundary point when both radial distances are positive. -/
theorem radialFrameCurve_injOn (c : Plane) {R : ℝ → ℝ} (hpos : ∀ s, 0 < R s) :
    InjOn (radialFrameCurve c R) (Ico (-Real.pi) Real.pi) := by
  intro s hs t ht h
  change c + circleMap 0 (R s) s = c + circleMap 0 (R t) t at h
  have heq := add_left_cancel h
  have hrad := congrArg norm heq
  simp only [norm_circleMap_zero, abs_of_pos (hpos _)] at hrad
  rw [← hrad] at heq
  exact injOn_circleMap_of_abs_sub_le' (hpos s).ne' (by linarith : Real.pi - (-Real.pi) ≤ 2*Real.pi) hs ht heq

/-- The polar realization discharges regularity, simplicity, and the
identification of the arclength curve. -/
theorem radialFrame_arclength_blowup (c : Plane) (R : ℝ → ℝ) (hR : ContDiff ℝ 1 R)
    (hpos : ∀ s, 0 < R s) (hend : R (-Real.pi) = R Real.pi)
    {t : ℝ} (ht : t ∈ Icc (-Real.pi) Real.pi)
    {β : ℝ → ℝ} (hβ : Continuous β) {M : ℝ} (hM : 0 < M) (hcut : ∀ y, M ≤ y → β y = 0) :
    Tendsto (fun ε : ℝ => ε⁻¹ * ∫ z, β (‖z-radialFrameCurve c R t‖ / ε)
      ∂curveArclength (radialFrameCurve c R) (-Real.pi) Real.pi)
      (𝓝[>] 0) (𝓝 (∫ y : ℝ, β |y|)) :=
  curveArclength_radial_blowup (radialFrameCurve_contDiff c hR) (neg_lt_self Real.pi_pos)
    (radialFrameCurve_closed c hend) (radialFrameCurve_injOn c hpos)
    (fun s _ => norm_pos_iff.mp (radialFrameCurve_speed_pos c hR hpos s)) ht hβ hM hcut

/-- Every physical boundary observation has the full-line limit, without a
choice of angular parameter in the conclusion. -/
theorem frontier_arclength_blowup (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ))
    {p : Plane} (hp : p ∈ frontier D.carrier)
    {β : ℝ → ℝ} (hβ : Continuous β) {M : ℝ} (hM : 0 < M) (hcut : ∀ y, M ≤ y → β y = 0) :
    Tendsto (fun ε : ℝ => ε⁻¹ * ∫ z, β (‖z-p‖ / ε)
      ∂curveArclength (radialFrameCurve c R) (-Real.pi) Real.pi)
      (𝓝[>] 0) (𝓝 (∫ y : ℝ, β |y|)) := by
  rw [← radialFrameCurve_image_eq_frontier D c R hR hpos hmem] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  exact radialFrame_arclength_blowup c R hR hpos hend ht hβ hM hcut

/-- The fixed radius-one physical probe has exactly the same boundary
normalization as in the half-plane volume calculation. -/
theorem frontier_arclength_radialKernelRaw (D : ConvexDomain) (c : Plane) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 1 R) (hpos : ∀ θ, 0 < R θ) (hend : R (-Real.pi) = R Real.pi)
    (hmem : ∀ θ ∈ Ioo (-Real.pi) Real.pi, ∀ r : ℝ, 0 < r →
      (c + circleMap 0 r θ ∈ D.carrier ↔ r < R θ))
    {p : Plane} (hp : p ∈ frontier D.carrier) :
    Tendsto (fun ε : ℝ => ε⁻¹ * ∫ z, WeakHarmonicRegularity.radialKernelRaw 1 (ε⁻¹ • (z-p))
      ∂curveArclength (radialFrameCurve c R) (-Real.pi) Real.pi)
      (𝓝[>] 0) (𝓝 (2 * ∫ y in Ioi (0 : ℝ), boundaryBumpProfile y)) := by
  have h := frontier_arclength_blowup D c R hR hpos hend hmem hp
    boundaryBumpProfile_continuous (by norm_num : (0:ℝ) < 1)
    (fun y hy => boundaryBumpProfile_zero (hy.trans (le_abs_self y)))
  rw [integral_comp_abs] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he : 0 < ε := hε
  simp only [boundaryBumpProfile_ramp, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos he, div_eq_inv_mul]

end Torsion.HermiteHadamard

import Torsion.WeakHarmonicWeyl.Associativity

/-! # Pointwise smoothing bounds and L² continuity

The actual Bochner convolution is bounded by the product of genuine L²
norms. Thus global L² convergence gives pointwise convergence of the fixed
smooth representative and all its fixed-kernel derivatives.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Torsion.WeakHarmonicRegularity

/-- Vector-valued L² Cauchy--Schwarz for the actual scalar-vector integral. -/
theorem norm_integral_smul_le_L2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a : Plane → ℝ} {b : Plane → E}
    (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    ‖∫ x, a x • b x‖ ≤ ‖ha.toLp a‖ * ‖hb.toLp b‖ := by
  have hi : inner (𝕜 := ℝ) (ha.norm.toLp (fun x => ‖a x‖))
      (hb.norm.toLp (fun x => ‖b x‖)) = ∫ x, ‖a x‖ * ‖b x‖ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.norm.coeFn_toLp, hb.norm.coeFn_toLp] with x ha hb
    rw [ha, hb]
    simp [mul_comm]
  calc
    _ ≤ ∫ x, ‖a x • b x‖ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖a x‖ * ‖b x‖ := by simp only [norm_smul]
    _ = inner (𝕜 := ℝ) (ha.norm.toLp (fun x => ‖a x‖))
        (hb.norm.toLp (fun x => ‖b x‖)) := hi.symm
    _ ≤ |inner (𝕜 := ℝ) (ha.norm.toLp (fun x => ‖a x‖))
        (hb.norm.toLp (fun x => ‖b x‖))| := le_abs_self _
    _ ≤ ‖ha.norm.toLp (fun x => ‖a x‖)‖ * ‖hb.norm.toLp (fun x => ‖b x‖)‖ :=
      abs_real_inner_le_norm _ _
    _ = _ := by simp only [Lp.norm_toLp, eLpNorm_norm]

/-- Every point of a fixed-kernel convolution is bounded by the same product
of L² norms, independently of the point of evaluation. -/
theorem norm_mollifyGradient_le_L2 {g : Plane → Plane} {κ : Plane → ℝ}
    (hg : MemLp g 2 volume) (hκ : MemLp κ 2 volume) (x : Plane) :
    ‖mollifyGradient g κ x‖ ≤ ‖hκ.toLp κ‖ * ‖hg.toLp g‖ := by
  have hmp : MeasurePreserving (fun t : Plane => x - t) volume volume :=
    (measurePreserving_add_left volume x).comp (Measure.measurePreserving_neg volume)
  have hA : MemLp (fun t : Plane => κ (x - t)) 2 volume := hκ.comp_measurePreserving hmp
  have hnorm : ‖hA.toLp (fun t : Plane => κ (x - t))‖ = ‖hκ.toLp κ‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp]
    congr 1
    exact eLpNorm_comp_measurePreserving hκ.1 hmp
  change ‖∫ t, κ (x - t) • g t‖ ≤ _
  simpa only [hnorm] using norm_integral_smul_le_L2 hA hg

/-- L² convergence to zero implies convergence to zero at every point after
smoothing by a fixed L² kernel. The estimate is uniform in that point. -/
theorem mollifyGradient_tendsto_zero_of_eLpNorm
    {g : ℕ → Plane → Plane} {κ : Plane → ℝ}
    (hg : ∀ n, MemLp (g n) 2 volume) (hκ : MemLp κ 2 volume)
    (hlim : Tendsto (fun n => eLpNorm (g n) 2 volume) atTop (𝓝 0)) (x : Plane) :
    Tendsto (fun n => mollifyGradient (g n) κ x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hreal : Tendsto (fun n => ‖(hg n).toLp (g n)‖) atTop (𝓝 0) := by
    simp only [Lp.norm_toLp]
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hreal.const_mul ‖hκ.toLp κ‖)
  · intro n
    exact norm_nonneg _
  · intro n
    simpa only [Lp.norm_toLp] using norm_mollifyGradient_le_L2 (hg n) hκ x

/-- Difference transport through a fixed smooth compact kernel is an actual
Bochner integral identity, valid for arbitrary L² representatives. -/
theorem mollifyGradient_sub {g h : Plane → Plane} {κ : Plane → ℝ}
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hκ : Continuous κ) (hc : HasCompactSupport κ) (x : Plane) :
    mollifyGradient (fun t => g t - h t) κ x =
      mollifyGradient g κ x - mollifyGradient h κ x := by
  have hi : Integrable (fun t => κ (x - t) • g t) volume :=
    hc.convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Plane →L[ℝ] Plane).flip
      (hg.locallyIntegrable (by norm_num)) hκ x
  have hj : Integrable (fun t => κ (x - t) • h t) volume :=
    hc.convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Plane →L[ℝ] Plane).flip
      (hh.locallyIntegrable (by norm_num)) hκ x
  change (∫ t, κ (x - t) • (g t - h t)) =
    (∫ t, κ (x - t) • g t) - ∫ t, κ (x - t) • h t
  simp_rw [smul_sub]
  exact integral_sub hi hj

/-- Strong L² convergence gives actual pointwise convergence of fixed
smoothings. This is the quantitative input to marked-derivative exhaustion. -/
theorem mollifyGradient_tendsto_of_eLpNorm_sub
    {g : ℕ → Plane → Plane} {h : Plane → Plane} {κ : Plane → ℝ}
    (hg : ∀ n, MemLp (g n) 2 volume) (hh : MemLp h 2 volume)
    (hκ : Continuous κ) (hc : HasCompactSupport κ)
    (hlim : Tendsto (fun n => eLpNorm (fun t => g n t - h t) 2 volume) atTop (𝓝 0))
    (x : Plane) :
    Tendsto (fun n => mollifyGradient (g n) κ x) atTop (𝓝 (mollifyGradient h κ x)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  have h := mollifyGradient_tendsto_zero_of_eLpNorm
    (fun n => (hg n).sub hh) (hκ.memLp_of_hasCompactSupport hc) hlim x
  exact h.congr' (Eventually.of_forall fun n => mollifyGradient_sub (hg n) hh hκ hc x)

end Torsion.WeakHarmonicRegularity

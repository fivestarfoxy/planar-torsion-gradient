import Torsion.WeakHarmonicWeyl.ConvolutionEstimates
import Torsion.WeakReflection

/-!
# Fixed smoothing kernels under parameter-dependent strong L² limits

These are arbitrary-filter versions of the existing sequential convolution
estimates. The reflection estimate retains the actual weak gradients and
therefore applies to Sobolev difference quotients without assuming boundary
derivative convergence.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.WeakHarmonicRegularity

/-- Fixed L² smoothing carries an arbitrary-filter strong L² zero limit to
an actual pointwise zero limit. -/
theorem mollifyGradient_tendsto_zero_of_eLpNorm_filter
    {A : Type*} {l : Filter A} {g : A → Plane → Plane} {κ : Plane → ℝ}
    (hg : ∀ a, MemLp (g a) 2 volume) (hκ : MemLp κ 2 volume)
    (hlim : Tendsto (fun a => eLpNorm (g a) 2 volume) l (𝓝 0)) (x : Plane) :
    Tendsto (fun a => mollifyGradient (g a) κ x) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hreal : Tendsto (fun a => ‖(hg a).toLp (g a)‖) l (𝓝 0) := by
    simp only [Lp.norm_toLp]
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hreal.const_mul ‖hκ.toLp κ‖)
  · intro a
    exact norm_nonneg _
  · intro a
    simpa only [Lp.norm_toLp] using norm_mollifyGradient_le_L2 (hg a) hκ x

/-- Strong L² convergence with an arbitrary parameter filter gives
pointwise convergence after a fixed smooth compact smoothing. -/
theorem mollifyGradient_tendsto_of_eLpNorm_sub_filter
    {A : Type*} {l : Filter A} {g : A → Plane → Plane} {h : Plane → Plane}
    {κ : Plane → ℝ}
    (hg : ∀ a, MemLp (g a) 2 volume) (hh : MemLp h 2 volume)
    (hκ : Continuous κ) (hc : HasCompactSupport κ)
    (hlim : Tendsto (fun a => eLpNorm (fun z => g a z - h z) 2 volume) l (𝓝 0))
    (x : Plane) :
    Tendsto (fun a => mollifyGradient (g a) κ x) l
      (𝓝 (mollifyGradient h κ x)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  have hz := mollifyGradient_tendsto_zero_of_eLpNorm_filter
    (fun a => (hg a).sub hh) (hκ.memLp_of_hasCompactSupport hc) hlim x
  exact hz.congr' (Eventually.of_forall fun a => mollifyGradient_sub (hg a) hh hκ hc x)

/-- Scalar multiplication commutes with the actual vector-valued smoothing
integral; this includes Sobolev difference-quotient coefficients. -/
theorem mollifyGradient_smul (g : Plane → Plane) (κ : Plane → ℝ)
    (c : ℝ) (x : Plane) :
    mollifyGradient (fun z => c • g z) κ x = c • mollifyGradient g κ x := by
  change (∫ z, κ (x-z) • (c • g z)) = c • ∫ z, κ (x-z) • g z
  calc
    _ = ∫ z, c • (κ (x-z) • g z) := by
      exact integral_congr_ae (ae_of_all _ fun z => smul_comm _ _ _)
    _ = _ := integral_smul c _

end Torsion.WeakHarmonicRegularity

namespace Torsion

/-- Reflection commutes with real scalar multiplication of the actual
weak-gradient representative. -/
theorem reflectedGradient_smul (g : Plane → Plane) (c : ℝ) :
    reflectedGradient (fun z => c • g z) = fun z => c • reflectedGradient g z := by
  funext z
  simp [reflectedGradient]

/-- Reflection commutes with subtraction of weak-gradient representatives. -/
theorem reflectedGradient_sub (g h : Plane → Plane) :
    reflectedGradient (fun z => g z - h z) =
      fun z => reflectedGradient g z - reflectedGradient h z := by
  funext z
  simp [reflectedGradient]

/-- Reflection of a weak planar gradient preserves every actual Lᵖ seminorm. -/
theorem eLpNorm_reflectedGradient (g : Plane → Plane) (p : ℝ≥0∞) :
    eLpNorm (reflectedGradient g) p volume = eLpNorm g p volume := by
  calc
    _ = eLpNorm (fun z => g (star z)) p volume := by
      apply eLpNorm_congr_norm_ae
      exact ae_of_all _ fun z => norm_star _
    _ = _ := eLpNorm_comp_conjugation g p

/-- Odd reflection is continuous for arbitrary strong L² parameter limits. -/
theorem oddGradient_tendsto_eLpNorm_sub_filter
    {A : Type*} {l : Filter A} {g : A → Plane → Plane} {h : Plane → Plane}
    (hg : ∀ a, MemLp (g a) 2 volume) (hh : MemLp h 2 volume)
    (hlim : Tendsto (fun a => eLpNorm (fun z => g a z - h z) 2 volume) l (𝓝 0)) :
    Tendsto (fun a => eLpNorm
      (fun z => (g a z - reflectedGradient (g a) z) -
        (h z - reflectedGradient h z)) 2 volume) l (𝓝 0) := by
  let k : A → Plane → Plane := fun a z => g a z - h z
  have hk (a : A) : MemLp (k a) 2 volume := (hg a).sub hh
  have heq (a : A) :
      (fun z => (g a z - reflectedGradient (g a) z) -
        (h z - reflectedGradient h z)) =
      (fun z => k a z - reflectedGradient (k a) z) := by
    funext z
    simp only [k, reflectedGradient, star_sub]
    abel
  have hbound (a : A) : eLpNorm (fun z => k a z - reflectedGradient (k a) z) 2 volume ≤
      eLpNorm (k a) 2 volume + eLpNorm (k a) 2 volume := by
    have hb := eLpNorm_sub_le (hk a).1 (memLp_reflectedGradient (hk a)).1
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa only [eLpNorm_reflectedGradient] using hb
  simp_rw [heq]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hlim.add hlim) (fun _ => zero_le _) hbound

/-- A fixed smoothing of the actual odd weak gradient converges pointwise
under an arbitrary-filter strong L² limit of the original gradients. -/
theorem mollifyOddGradient_tendsto_of_eLpNorm_sub_filter
    {A : Type*} {l : Filter A} {g : A → Plane → Plane} {h : Plane → Plane}
    {κ : Plane → ℝ}
    (hg : ∀ a, MemLp (g a) 2 volume) (hh : MemLp h 2 volume)
    (hκ : Continuous κ) (hc : HasCompactSupport κ)
    (hlim : Tendsto (fun a => eLpNorm (fun z => g a z - h z) 2 volume) l (𝓝 0))
    (x : Plane) :
    Tendsto (fun a => WeakHarmonicRegularity.mollifyGradient
      (fun z => g a z - reflectedGradient (g a) z) κ x) l
      (𝓝 (WeakHarmonicRegularity.mollifyGradient
        (fun z => h z - reflectedGradient h z) κ x)) := by
  exact WeakHarmonicRegularity.mollifyGradient_tendsto_of_eLpNorm_sub_filter
    (fun a => (hg a).sub (memLp_reflectedGradient (hg a)))
    (hh.sub (memLp_reflectedGradient hh)) hκ hc
    (oddGradient_tendsto_eLpNorm_sub_filter hg hh hlim) x

/-- The local parameter version needs L² admission only eventually. Values
outside the parameter neighborhood play no role in the actual smoothing limit. -/
theorem mollifyOddGradient_tendsto_of_eLpNorm_sub_filter_eventually
    {A : Type*} {l : Filter A} {g : A → Plane → Plane} {h : Plane → Plane}
    {κ : Plane → ℝ}
    (hg : ∀ᶠ a in l, MemLp (g a) 2 volume) (hh : MemLp h 2 volume)
    (hκ : Continuous κ) (hc : HasCompactSupport κ)
    (hlim : Tendsto (fun a => eLpNorm (fun z => g a z - h z) 2 volume) l (𝓝 0))
    (x : Plane) :
    Tendsto (fun a => WeakHarmonicRegularity.mollifyGradient
      (fun z => g a z - reflectedGradient (g a) z) κ x) l
      (𝓝 (WeakHarmonicRegularity.mollifyGradient
        (fun z => h z - reflectedGradient h z) κ x)) := by
  classical
  let G : A → Plane → Plane := fun a => if MemLp (g a) 2 volume then g a else h
  have hG (a : A) : MemLp (G a) 2 volume := by
    by_cases ha : MemLp (g a) 2 volume
    · simpa only [G, if_pos ha] using ha
    · simpa only [G, if_neg ha] using hh
  have heq : G =ᶠ[l] g := hg.mono fun a ha => by simp only [G, if_pos ha]
  have hGlim : Tendsto (fun a => eLpNorm (fun z => G a z - h z) 2 volume) l (𝓝 0) :=
    hlim.congr' (heq.mono fun a ha => by simp only [ha])
  exact (mollifyOddGradient_tendsto_of_eLpNorm_sub_filter hG hh hκ hc hGlim x).congr'
    (heq.mono fun a ha => by simp only [ha])

end Torsion

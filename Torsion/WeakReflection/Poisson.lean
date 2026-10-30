module

public import Torsion.WeakReflection.Odd

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The marked Poisson correction and actual harmonic odd extension

Adding y²/2 cancels the torsion forcing near the flat boundary. A compact
smooth cutoff makes this a genuine global H¹ pair, whose upper restriction
has the proved zero trace. Odd reflection then gives a weakly harmonic pair
on the whole marked ball.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

def quadraticIm (z : Plane) : ℝ := z.im ^ 2 / 2

theorem quadraticIm_contDiff : ContDiff ℝ ∞ quadraticIm :=
  (Complex.imCLM.contDiff.pow 2).div_const 2

theorem hasGradientAt_quadraticIm (z : Plane) :
    HasGradientAt quadraticIm ((z.im : ℂ) * Complex.I) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hi := Complex.imCLM.hasFDerivAt (x := z)
  convert (hi.mul hi).const_smul (1 / 2 : ℝ) using 1
  · ext w
    change w.im ^ 2 / 2 = (1 / 2 : ℝ) * (w.im * w.im)
    ring
  · ext v
    simp [InnerProductSpace.toDual_apply_apply, Complex.inner, Complex.mul_re]
    ring

theorem gradient_quadraticIm (z : Plane) :
    gradient quadraticIm z = (z.im : ℂ) * Complex.I :=
  (hasGradientAt_quadraticIm z).gradient

/-- The exact integration-by-parts identity cancelling the torsion forcing.
It applies to the actual compact test, without a PDE or Green assumption. -/
theorem IsTest.quadraticIm_pairing {D : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTest D ψ) :
    (∫ z, inner (𝕜 := ℝ) ((z.im : ℂ) * Complex.I) (gradient ψ z)) = - ∫ z, ψ z := by
  have hd (z : Plane) : fderiv ℝ (fun x : Plane => x.im) z Complex.I = 1 := by
    change fderiv ℝ Complex.imCLM z Complex.I = 1
    rw [Complex.imCLM.fderiv]
    rfl
  have hψdir : HasCompactSupport (fun z => fderiv ℝ ψ z Complex.I) := by
    exact hψ.2.1.fderiv_apply ℝ Complex.I
  have hψdirc : Continuous (fun z => fderiv ℝ ψ z Complex.I) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : Integrable (fun z => fderiv ℝ (fun x : Plane => x.im) z Complex.I * ψ z) volume := by
    simpa only [hd, one_mul] using
      hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have h2 : Integrable (fun z => z.im * fderiv ℝ ψ z Complex.I) volume :=
    (Complex.continuous_im.mul hψdirc).integrable_of_hasCompactSupport hψdir.mul_left
  have h3 : Integrable (fun z => z.im * ψ z) volume :=
    (Complex.continuous_im.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
  have heq := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => Complex.imCLM.differentiable x)
    (fun x _ => hψ.1.differentiable (by simp) x)
  simp only [hd, one_mul, fderiv_apply_eq_inner_gradient] at heq
  convert heq using 1
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    change inner (𝕜 := ℝ) ((z.im : ℂ) * Complex.I) (gradient ψ z) =
      z.im * inner (𝕜 := ℝ) (gradient ψ z) Complex.I
    rw [← Complex.real_smul, real_inner_smul_left, real_inner_comm]

/-- The torsion solution at a flat marked patch admits an actual compact
quadratic correction whose odd extension is weakly harmonic on a full ball.
Only weak torsion and the stated geometric inclusions are required. -/
theorem IsWeakTorsion.exists_odd_harmonic_correction
    {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hDH : D ⊆ upperHalfPlane) (r : ℝ)
    (hHD : upperHalfPlane ∩ Metric.ball 0 r ⊆ D) :
    ∃ p : Plane → ℝ, IsTest univ p ∧
      (∀ z ∈ Metric.ball (0 : Plane) r, p z = quadraticIm z) ∧
      (∀ x : ℝ, p (x : ℂ) = 0) ∧
      MemH10 upperHalfPlane (fun z => u z + upperHalfPlane.indicator p z)
        (fun z => g z + upperHalfPlane.indicator (gradient p) z) ∧
      IsWeakHarmonicOn (Metric.ball 0 r)
        (fun z => (u z + upperHalfPlane.indicator p z) -
          reflectedValue (fun x => u x + upperHalfPlane.indicator p x) z)
        (fun z => (g z + upperHalfPlane.indicator (gradient p) z) -
          reflectedGradient (fun x => g x + upperHalfPlane.indicator (gradient p) x) z) := by
  obtain ⟨η, hη, hηone⟩ := exists_test_eq_one_near_compact isOpen_univ
    (isCompact_closedBall (0 : Plane) r) (subset_univ _)
  let p : Plane → ℝ := fun z => η z * quadraticIm z
  have hp : IsTest univ p := hη.mul_left quadraticIm_contDiff
  have hpNear {z : Plane} (hz : z ∈ Metric.ball (0 : Plane) r) :
      p =ᶠ[𝓝 z] quadraticIm := by
    have heq := hηone.filter_mono
      (nhds_le_nhdsSet (Metric.ball_subset_closedBall hz))
    filter_upwards [heq] with x hx
    simp only [p, hx, one_mul]
  have hpEq (z : Plane) (hz : z ∈ Metric.ball (0 : Plane) r) :
      p z = quadraticIm z := (hpNear hz).self_of_nhds
  have hpG (z : Plane) (hz : z ∈ Metric.ball (0 : Plane) r) :
      gradient p z = (z.im : ℂ) * Complex.I := by
    unfold gradient
    rw [(hpNear hz).fderiv_eq]
    exact gradient_quadraticIm z
  have hpzero (x : ℝ) : p (x : ℂ) = 0 := by simp [p, quadraticIm]
  have hpH := hp.upperHalfPlane_indicator_of_zero_axis hpzero
  have hpair := (hu.1.mono hDH).add hpH
  have hw : IsWeakHarmonicOn (upperHalfPlane ∩ Metric.ball 0 r)
      (fun z => u z + upperHalfPlane.indicator p z)
      (fun z => g z + upperHalfPlane.indicator (gradient p) z) := by
    refine ⟨hpair.distributionalGradient, ?_⟩
    intro ψ hψ
    have hU := hu.global_smooth_test_equation (hψ.mono hHD)
    have hP : (∫ z, inner (𝕜 := ℝ) (upperHalfPlane.indicator (gradient p) z)
        (gradient ψ z)) = - ∫ z, ψ z := by
      convert hψ.quadraticIm_pairing using 1
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change inner (𝕜 := ℝ) (upperHalfPlane.indicator (gradient p) z) (gradient ψ z) =
          inner (𝕜 := ℝ) ((z.im : ℂ) * Complex.I) (gradient ψ z)
        by_cases hz : z ∈ upperHalfPlane ∩ Metric.ball 0 r
        · rw [indicator_of_mem hz.1, hpG z hz.2]
        · have hnot : z ∉ tsupport ψ := fun h => hz (hψ.2.2 h)
          rw [gradient_eq_zero_of_not_mem_tsupport hnot]
          simp
    have hi := integrable_real_inner_of_memLp_two hu.1.2.1 (hψ.memLp_gradient (p := 2))
    have hip := integrable_real_inner_of_memLp_two hpH.2.1 (hψ.memLp_gradient (p := 2))
    simp only [inner_add_left]
    rw [integral_add hi hip, hU, hP, add_neg_cancel]
  exact ⟨p, hp, hpEq, hpzero, hpair, hw.odd_reflection hpair⟩

/-- The preceding construction packaged as a single actual weakly harmonic
odd pair, equal to u+y²/2 in the upper marked half-ball. -/
theorem IsWeakTorsion.exists_odd_harmonic_extension
    {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hDH : D ⊆ upperHalfPlane) (r : ℝ)
    (hHD : upperHalfPlane ∩ Metric.ball 0 r ⊆ D) :
    ∃ (w : Plane → ℝ) (h : Plane → Plane), MemH10 univ w h ∧
      IsWeakHarmonicOn (Metric.ball 0 r) w h ∧
      (w =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 r)]
        fun z => u z + quadraticIm z) ∧
      (∀ z, w (star z) = -w z) := by
  obtain ⟨p, hp, hpEq, hpzero, hpair, hw⟩ :=
    hu.exists_odd_harmonic_correction hDH r hHD
  let w : Plane → ℝ := fun z => (u z + upperHalfPlane.indicator p z) -
    reflectedValue (fun x => u x + upperHalfPlane.indicator p x) z
  let h : Plane → Plane := fun z => (g z + upperHalfPlane.indicator (gradient p) z) -
    reflectedGradient (fun x => g x + upperHalfPlane.indicator (gradient p) x) z
  have hmem : MemH10 univ w h :=
    (hpair.mono (subset_univ _)).sub (hpair.reflectedValue.mono (subset_univ _))
  refine ⟨w, h, hmem, hw, ?_, ?_⟩
  · have hupper := ae_restrict_of_ae_restrict_of_subset
      (inter_subset_left : upperHalfPlane ∩ Metric.ball 0 r ⊆ upperHalfPlane)
      hpair.odd_reflection_ae_upper
    filter_upwards [hupper, ae_restrict_mem
      (((isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball).measurableSet)]
      with z hz hzU
    dsimp only [w]
    rw [hz, indicator_of_mem hzU.1, hpEq z hzU.2]
  · intro z
    simp only [w, reflectedValue, star_star]
    ring

/-- The odd extension with its actual weak-gradient identification retained.
This stronger form supplies both coordinates of local torsion regularity. -/
theorem IsWeakTorsion.exists_odd_harmonic_extension_with_gradient
    {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hDH : D ⊆ upperHalfPlane) (r : ℝ)
    (hHD : upperHalfPlane ∩ Metric.ball 0 r ⊆ D) :
    ∃ (w : Plane → ℝ) (h : Plane → Plane), MemH10 univ w h ∧
      IsWeakHarmonicOn (Metric.ball 0 r) w h ∧
      (w =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 r)]
        fun z => u z + quadraticIm z) ∧
      (h =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 r)]
        fun z => g z + gradient quadraticIm z) ∧
      (∀ z, w (star z) = -w z) := by
  obtain ⟨p, hp, hpEq, hpzero, hpair, hw⟩ :=
    hu.exists_odd_harmonic_correction hDH r hHD
  let w : Plane → ℝ := fun z => (u z + upperHalfPlane.indicator p z) -
    reflectedValue (fun x => u x + upperHalfPlane.indicator p x) z
  let h : Plane → Plane := fun z => (g z + upperHalfPlane.indicator (gradient p) z) -
    reflectedGradient (fun x => g x + upperHalfPlane.indicator (gradient p) x) z
  have hmem : MemH10 univ w h :=
    (hpair.mono (subset_univ _)).sub (hpair.reflectedValue.mono (subset_univ _))
  have hU : MeasurableSet (upperHalfPlane ∩ Metric.ball (0 : Plane) r) :=
    ((isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball).measurableSet
  have hpG {z : Plane} (hz : z ∈ Metric.ball (0 : Plane) r) :
      gradient p z = gradient quadraticIm z := by
    have heq : p =ᶠ[𝓝 z] quadraticIm := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with x hx
      exact hpEq x hx
    unfold gradient
    rw [heq.fderiv_eq]
  refine ⟨w, h, hmem, hw, ?_, ?_, ?_⟩
  · have hupper := ae_restrict_of_ae_restrict_of_subset
      (inter_subset_left : upperHalfPlane ∩ Metric.ball 0 r ⊆ upperHalfPlane)
      hpair.odd_reflection_ae_upper
    filter_upwards [hupper, ae_restrict_mem hU] with z hz hzU
    dsimp only [w]
    rw [hz, indicator_of_mem hzU.1, hpEq z hzU.2]
  · have hupper := ae_restrict_of_ae_restrict_of_subset
      (inter_subset_left : upperHalfPlane ∩ Metric.ball 0 r ⊆ upperHalfPlane)
      hpair.odd_reflection_gradient_ae_upper
    filter_upwards [hupper, ae_restrict_mem hU] with z hz hzU
    dsimp only [h]
    rw [hz, indicator_of_mem hzU.1, hpG hzU.2]
  · intro z
    simp only [w, reflectedValue, star_star]
    ring

/-- Every marked torsion problem has the actual full-ball weakly harmonic
odd correction required by the ordinary interior Weyl argument. -/
theorem IsMarked.exists_odd_harmonic_torsion_extension
    {D : Set Plane} (hD : IsMarked D) {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) :
    ∃ (r : ℝ) (w : Plane → ℝ) (h : Plane → Plane), 0 < r ∧
      MemH10 univ w h ∧ IsWeakHarmonicOn (Metric.ball 0 r) w h ∧
      (w =ᵐ[volume.restrict (upperHalfPlane ∩ Metric.ball 0 r)]
        fun z => u z + quadraticIm z) ∧ (∀ z, w (star z) = -w z) := by
  obtain ⟨r, hr, hflat⟩ := hD.2.2.2
  have hHD : upperHalfPlane ∩ Metric.ball 0 r ⊆ D := by
    intro z hz
    rw [← hflat] at hz
    exact hz.1
  obtain ⟨w, h, hmem, hw, hAE, hodd⟩ := hu.exists_odd_harmonic_extension hD.2.2.1 r hHD
  exact ⟨r, w, h, hr, hmem, hw, hAE, hodd⟩

end Torsion

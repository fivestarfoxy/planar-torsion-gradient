module

public import Torsion.RestrictedSpectralOddFold
public import Torsion.RestrictedSpectralOddGagliardo

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual smooth core approximants for odd folding

A scalar map which vanishes on a value neighborhood of zero can be folded
by the spatial sign while remaining smooth at the origin of an odd smooth
density. Its actual support does not increase. This proves membership in
the original compact smooth restricted core for the flat approximants.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- The odd spatial fold is genuinely smooth when its scalar composition
vanishes near the zero value at the origin. -/
theorem contDiff_oddFoldComp_of_zero_near {Φ f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hodd : Function.Odd f) (hΦ : ContDiff ℝ ∞ Φ)
    {ε : ℝ} (hε : 0 < ε) (hzero : ∀ t : ℝ, |t| ≤ ε → Φ t = 0) :
    ContDiff ℝ ∞ (oddFoldComp Φ f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · apply (hΦ.comp hf).neg.contDiffAt.congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hx] with t ht
    change t < 0 at ht
    simp only [oddFoldComp, if_neg (not_le.mpr ht), Function.comp_apply]
  · subst x
    have hf0 : f 0 = 0 := by
      have ho := hodd 0
      simp only [neg_zero] at ho
      linarith
    have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |f t| < ε := by
      simpa only [Real.norm_eq_abs] using
        (hf.continuous.norm.tendsto (0 : ℝ)).eventually
          (eventually_lt_nhds (show ‖f 0‖ < ε from by simpa only [hf0, norm_zero] using hε))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hsmall] with t ht
    have hzt := hzero (f t) ht.le
    simp [oddFoldComp, hzt]
  · apply (hΦ.comp hf).contDiffAt.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
    change 0 < t at ht
    simp only [oddFoldComp, if_pos ht.le, Function.comp_apply]

/-- The actual topological support of a zero-fixing odd fold is contained
in the original support. -/
theorem tsupport_oddFoldComp_subset {Φ f : ℝ → ℝ} (hΦ0 : Φ 0 = 0) :
    tsupport (oddFoldComp Φ f) ⊆ tsupport f := by
  apply closure_mono
  intro x hx
  by_contra hfx
  have hf0 : f x = 0 := not_ne_iff.mp hfx
  exact hx (by simp [oddFoldComp, hf0, hΦ0])

/-- A flat scalar composition of an odd actual restricted core function
remains in that same concrete core. -/
theorem IsCore.oddFoldComp_of_zero_near {Φ f : ℝ → ℝ}
    (hf : IsCore f) (hodd : Function.Odd f) (hΦ : ContDiff ℝ ∞ Φ)
    {ε : ℝ} (hε : 0 < ε) (hzero : ∀ t : ℝ, |t| ≤ ε → Φ t = 0) :
    IsCore (oddFoldComp Φ f) := by
  have hΦ0 : Φ 0 = 0 := hzero 0 (by simpa using hε.le)
  have hsupport := tsupport_oddFoldComp_subset (f := f) hΦ0
  exact ⟨contDiff_oddFoldComp_of_zero_near hf.1 hodd hΦ hε hzero,
    hf.2.1.of_isClosed_subset (isClosed_tsupport _) hsupport,
    hsupport.trans hf.2.2⟩

/-- The explicit flat approximants to odd absolute folding are original
compact smooth restricted core functions. -/
theorem IsCore.oddFoldAbsApprox {f : ℝ → ℝ}
    (hf : IsCore f) (hodd : Function.Odd f) (n : ℕ) :
    IsCore (oddFoldComp (oddFoldAbsApprox n) f) :=
  hf.oddFoldComp_of_zero_near hodd (oddFoldAbsApprox_contDiff n) (oddFoldEpsilon_pos n)
    (fun _ ht => oddFoldAbsApprox_zero_on n ht)

/-- These actual smooth odd-fold approximants do not increase the original
Fourier energy, by the proved four-quadrant contraction. -/
theorem energy_oddFoldAbsApprox_le {f : ℝ → ℝ}
    (hf : IsCore f) (hodd : Function.Odd f) (n : ℕ) :
    energy (oddFoldComp (oddFoldAbsApprox n) f) (oddFoldComp (oddFoldAbsApprox n) f) ≤
      energy f f := by
  have hcore := hf.oddFoldAbsApprox hodd n
  have hG := gagliardoEnergy_folded_comp_le hf.1.continuous.measurable hodd
    hcore.1.continuous.measurable
    (oddFoldComp_odd hodd (oddFoldAbsApprox_even n) (oddFoldAbsApprox_zero n))
    (oddFoldAbsApprox_zero n)
    (fun u v => by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (oddFoldAbsApprox_lipschitz n).dist_le_mul u v)
    (fun x hx => by simp only [oddFoldComp, if_pos hx.le])
  rw [gagliardoEnergy_of_core hcore.1 hcore.2.1, gagliardoEnergy_of_core hf.1 hf.2.1] at hG
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg gagliardoSymbolConstant_pos.le (energy_nonneg f))).1 hG
  exact (mul_le_mul_iff_left₀ gagliardoSymbolConstant_pos).1 hreal

end Torsion.Spectral

module

public import Torsion.RestrictedSpectralGagliardoKernel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Strict absolute-value contraction and constant sign

Equality in the actual Markov contraction forces the two-point Gagliardo
gap to vanish almost everywhere. Its strictly positive off-diagonal kernel
then forces all nonzero values to have the same sign. This proves a genuine
irreducibility property of the original restricted Fourier form.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

private theorem gagliardoEnergy_eq_prod {f : ℝ → ℝ} (hf : Measurable f) :
    gagliardoEnergy f =
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((f p.2 - f p.1) ^ 2 / (p.2 - p.1) ^ 2) := by
  rw [gagliardoEnergy_eq_double hf]
  exact (lintegral_prod _ (measurable_gagliardoKernel hf).aemeasurable).symm

private def absGap (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * (|f p.2 * f p.1| - f p.2 * f p.1) / (p.2 - p.1) ^ 2

private theorem absGap_nonneg (f : ℝ → ℝ) (p : ℝ × ℝ) : 0 ≤ absGap f p := by
  exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.2 (le_abs_self _))) (sq_nonneg _)

private theorem measurable_absGap {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (absGap f p)) := by
  apply Measurable.ennreal_ofReal
  unfold absGap
  fun_prop

private theorem gagliardo_abs_gap {f : ℝ → ℝ} (hf : Measurable f) :
    gagliardoEnergy f = gagliardoEnergy (fun x => |f x|) +
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (absGap f p) := by
  have hpoint (p : ℝ × ℝ) :
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2 / (p.2 - p.1) ^ 2) =
        ENNReal.ofReal ((|f p.2| - |f p.1|) ^ 2 / (p.2 - p.1) ^ 2) +
          ENNReal.ofReal (absGap f p) := by
    have hnum : (f p.2 - f p.1) ^ 2 =
        (|f p.2| - |f p.1|) ^ 2 + 2 * (|f p.2 * f p.1| - f p.2 * f p.1) := by
      rw [abs_mul]
      nlinarith [sq_abs (f p.1), sq_abs (f p.2)]
    rw [hnum, add_div]
    exact ENNReal.ofReal_add (div_nonneg (sq_nonneg _) (sq_nonneg _)) (absGap_nonneg f p)
  have hfabs : Measurable (fun x => |f x|) := continuous_abs.measurable.comp hf
  rw [gagliardoEnergy_eq_prod hf, gagliardoEnergy_eq_prod hfabs]
  simp_rw [hpoint]
  exact lintegral_add_left (measurable_gagliardoKernel hfabs) _

/-- For a measurable finite-Gagliardo density, equality under absolute
value forces a single almost-everywhere sign. No spectral property is used. -/
theorem ae_sign_of_gagliardo_abs_eq {f : ℝ → ℝ} (hf : Measurable f)
    (hfinite : gagliardoEnergy f ≠ ∞)
    (heq : gagliardoEnergy (fun x => |f x|) = gagliardoEnergy f)
    (hne : ¬ f =ᵐ[volume] 0) : 0 ≤ᵐ[volume] f ∨ f ≤ᵐ[volume] 0 := by
  classical
  have habsfinite : gagliardoEnergy (fun x => |f x|) ≠ ∞ := by
    rw [heq]
    exact hfinite
  have hadd := gagliardo_abs_gap hf
  have hzero : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (absGap f p)) = 0 := by
    apply (ENNReal.add_right_inj habsfinite).1
    calc
      _ = gagliardoEnergy f := hadd.symm
      _ = gagliardoEnergy (fun x => |f x|) + 0 := by rw [← heq, add_zero]
  have hgap := (lintegral_eq_zero_iff (measurable_absGap hf)).1 hzero
  have hproduct : ∀ᵐ p : ℝ × ℝ ∂volume, 0 ≤ f p.2 * f p.1 := by
    filter_upwards [hgap] with p hp
    by_cases hdiag : p.2 = p.1
    · rw [hdiag]
      exact mul_self_nonneg _
    · have hquot : absGap f p ≤ 0 := ENNReal.ofReal_eq_zero.1 hp
      have hden : 0 < (p.2 - p.1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.2 hdiag)
      have hnum : 2 * (|f p.2 * f p.1| - f p.2 * f p.1) ≤ 0 := by
        simpa only [zero_mul] using (div_le_iff₀ hden).1 hquot
      have habs : |f p.2 * f p.1| = f p.2 * f p.1 := by linarith [le_abs_self (f p.2 * f p.1)]
      exact abs_eq_self.1 habs
  have hpair : ∀ᵐ x : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume, 0 ≤ f y * f x := Measure.ae_ae_of_ae_prod hproduct
  have hex : ∃ x : ℝ, (∀ᵐ y : ℝ ∂volume, 0 ≤ f y * f x) ∧ f x ≠ 0 := by
    by_contra hnot
    apply hne
    filter_upwards [hpair] with x hx
    change f x = 0
    by_contra hfx
    exact hnot ⟨x, hx, hfx⟩
  obtain ⟨x, hx, hfx⟩ := hex
  rcases lt_or_gt_of_ne hfx with hneg | hpos
  · right
    filter_upwards [hx] with y hy
    change f y ≤ 0
    exact nonpos_of_mul_nonneg_left hy hneg
  · left
    filter_upwards [hx] with y hy
    change 0 ≤ f y
    exact nonneg_of_mul_nonneg_left hy hpos

/-- Equality in the original actual Fourier absolute-value contraction
is equivalent to absence of an almost-everywhere sign change. -/
theorem energy_abs_eq_iff_sign {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f) :
    energy (fun x => |f x|) (fun x => |f x|) = energy f f ↔
      (0 ≤ᵐ[volume] f ∨ f ≤ᵐ[volume] 0) := by
  constructor
  · intro henergy
    by_cases hzero : f =ᵐ[volume] 0
    · left
      filter_upwards [hzero] with x hx
      change 0 ≤ f x
      simpa only [hx, Pi.zero_apply] using (le_refl (0 : ℝ))
    · let g := hf.1.1.mk f
      have hfg : f =ᵐ[volume] g := hf.1.1.ae_eq_mk
      have hg : Measurable g := hf.1.1.stronglyMeasurable_mk.measurable
      have hgform : MemRestrictedFormDomain g := hf.congr_ae hfg
      have habsfg : (fun x => |f x|) =ᵐ[volume] (fun x => |g x|) := hfg.fun_comp abs
      have hGeq : gagliardoEnergy (fun x => |g x|) = gagliardoEnergy g := by
        rw [← gagliardoEnergy_congr_ae habsfg, ← gagliardoEnergy_congr_ae hfg,
          hf.abs.gagliardoEnergy, hf.gagliardoEnergy, henergy]
      have hGfinite : gagliardoEnergy g ≠ ∞ := by rw [hgform.gagliardoEnergy]; exact ENNReal.ofReal_ne_top
      have hgne : ¬ g =ᵐ[volume] 0 := fun hz => hzero (hfg.trans hz)
      rcases ae_sign_of_gagliardo_abs_eq hg hGfinite hGeq hgne with hnonneg | hnonpos
      · left
        filter_upwards [hfg, hnonneg] with x hx hs
        change 0 ≤ f x
        rw [hx]
        exact hs
      · right
        filter_upwards [hfg, hnonpos] with x hx hs
        change f x ≤ 0
        rw [hx]
        exact hs
  · rintro (hnonneg | hnonpos)
    · have habs : (fun x => |f x|) =ᵐ[volume] f := by
        filter_upwards [hnonneg] with x hx
        exact abs_of_nonneg hx
      exact energy_congr_ae habs habs
    · have habs : (fun x => |f x|) =ᵐ[volume] (fun x => -f x) := by
        filter_upwards [hnonpos] with x hx
        exact abs_of_nonpos hx
      calc
        _ = energy (fun x => -f x) (fun x => -f x) := energy_congr_ae habs habs
        _ = energy f f := by simpa only [neg_one_mul, neg_sq, one_pow, one_mul] using energy_const_mul_self (-1) f

/-- Every actual sign-changing form member strictly lowers its Fourier
energy when replaced by its absolute value. -/
theorem energy_abs_lt_of_sign_changes {f : ℝ → ℝ} (hf : MemRestrictedFormDomain f)
    (hpos : ¬ 0 ≤ᵐ[volume] f) (hneg : ¬ f ≤ᵐ[volume] 0) :
    energy (fun x => |f x|) (fun x => |f x|) < energy f f := by
  apply lt_of_le_of_ne (energy_abs_le hf)
  intro heq
  rcases (energy_abs_eq_iff_sign hf).1 heq with hp | hn
  · exact hpos hp
  · exact hneg hn

end Torsion.Spectral

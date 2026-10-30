module

public import Torsion.RestrictedSpectralOddGap
public import Torsion.RestrictedSpectralOddLattice

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Strict folded-absolute contraction on the actual odd restricted form

The paired positive-half kernel has a strictly positive interaction weight
away from the diagonal. Equality in odd folded-absolute contraction forces
one almost-everywhere sign on the positive half-line. Measurable odd
representatives are constructed from the original L² classes.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

private def positiveHalfMeasure : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

private instance : SFinite positiveHalfMeasure := by
  unfold positiveHalfMeasure
  infer_instance

private def oddPairIntegral (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (oddGagliardoPair f p.1 p.2)
    ∂(positiveHalfMeasure.prod positiveHalfMeasure)

private theorem measurable_oddPair {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (oddGagliardoPair f p.1 p.2)) := by
  apply Measurable.ennreal_ofReal
  unfold oddGagliardoPair
  fun_prop

private theorem positive_quadrant_ae : ∀ᵐ p : ℝ × ℝ ∂positiveHalfMeasure.prod positiveHalfMeasure,
    0 < p.1 ∧ 0 < p.2 := by
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd))).2
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact ⟨hx, hy⟩

private theorem measurable_oddAbsGap {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (oddAbsGap f p.1 p.2)) := by
  apply Measurable.ennreal_ofReal
  unfold oddAbsGap
  fun_prop

private theorem gagliardoEnergy_eq_oddPairIntegral {f : ℝ → ℝ}
    (hf : Measurable f) (hodd : Function.Odd f) :
    gagliardoEnergy f = 2 * oddPairIntegral f := by
  rw [gagliardoEnergy_odd_eq_positive_pair hf hodd]
  congr 1
  exact (lintegral_prod _ (measurable_oddPair hf).aemeasurable).symm

private theorem oddPairIntegral_gap {f : ℝ → ℝ} (hf : Measurable f) :
    oddPairIntegral f = oddPairIntegral (oddFoldAbs f) +
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (oddAbsGap f p.1 p.2)
        ∂(positiveHalfMeasure.prod positiveHalfMeasure) := by
  have hfold : Measurable (oddFoldAbs f) := oddFoldComp_measurable continuous_abs.measurable hf
  unfold oddPairIntegral
  calc
    _ = ∫⁻ p : ℝ × ℝ,
        (ENNReal.ofReal (oddGagliardoPair (oddFoldAbs f) p.1 p.2) +
          ENNReal.ofReal (oddAbsGap f p.1 p.2)) ∂(positiveHalfMeasure.prod positiveHalfMeasure) := by
      apply lintegral_congr_ae
      filter_upwards [positive_quadrant_ae] with p hp
      have hpair := oddGagliardoPair_abs_gap f p.1 p.2
      have hfoldpair : oddGagliardoPair (oddFoldAbs f) p.1 p.2 =
          oddGagliardoPair (fun x => |f x|) p.1 p.2 := by
        unfold oddGagliardoPair
        rw [oddFoldAbs_of_nonneg hp.1.le, oddFoldAbs_of_nonneg hp.2.le]
      rw [hfoldpair, hpair]
      exact ENNReal.ofReal_add
        (add_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
          (div_nonneg (sq_nonneg _) (sq_nonneg _)))
        (oddAbsGap_nonneg f hp.1 hp.2)
    _ = _ := lintegral_add_left (measurable_oddPair hfold) _

/-- Exact nonnegative odd-fold energy gap. This quantitative identity is
available before any spectral assumption and retains the actual positive
half-plane interaction integral. -/
theorem gagliardoEnergy_oddFoldAbs_gap {f : ℝ → ℝ}
    (hf : Measurable f) (hodd : Function.Odd f) :
    gagliardoEnergy f = gagliardoEnergy (oddFoldAbs f) + 2 *
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (oddAbsGap f p.1 p.2)
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hfold : Measurable (oddFoldAbs f) := oddFoldComp_measurable continuous_abs.measurable hf
  rw [gagliardoEnergy_eq_oddPairIntegral hf hodd, oddPairIntegral_gap hf,
    gagliardoEnergy_eq_oddPairIntegral hfold (oddFoldAbs_odd hodd)]
  dsimp only [positiveHalfMeasure]
  ring

/-- The original Fourier energies satisfy the exact paired-gap identity
for every measurable actual odd form member. -/
theorem energy_oddFoldAbs_gap {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f) (hm : Measurable f) :
    ENNReal.ofReal (gagliardoSymbolConstant * energy f f) =
      ENNReal.ofReal (gagliardoSymbolConstant * energy (oddFoldAbs f) (oddFoldAbs f)) + 2 *
        ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (oddAbsGap f p.1 p.2)
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [← hf.gagliardoEnergy, ← (hf.oddFoldAbs hodd).gagliardoEnergy]
  exact gagliardoEnergy_oddFoldAbs_gap hm hodd

/-- Equality in the genuine odd Gagliardo fold forces a single a.e. sign
on the positive half-line, without a spectral assumption. -/
theorem ae_half_sign_of_gagliardo_oddFoldAbs_eq {f : ℝ → ℝ}
    (hf : Measurable f) (hodd : Function.Odd f)
    (hfinite : gagliardoEnergy f ≠ ∞)
    (heq : gagliardoEnergy (oddFoldAbs f) = gagliardoEnergy f) :
    0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f ∨ f ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  classical
  have hfold : Measurable (oddFoldAbs f) := oddFoldComp_measurable continuous_abs.measurable hf
  have hpairEq : oddPairIntegral (oddFoldAbs f) = oddPairIntegral f := by
    apply (ENNReal.mul_right_inj (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).1
    rw [← gagliardoEnergy_eq_oddPairIntegral hfold (oddFoldAbs_odd hodd),
      ← gagliardoEnergy_eq_oddPairIntegral hf hodd]
    exact heq
  have hpairFinite : oddPairIntegral (oddFoldAbs f) ≠ ∞ := by
    rw [hpairEq]
    intro htop
    apply hfinite
    rw [gagliardoEnergy_eq_oddPairIntegral hf hodd, htop]
    norm_num
  have hadd := oddPairIntegral_gap hf
  have hzero : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (oddAbsGap f p.1 p.2)
      ∂(positiveHalfMeasure.prod positiveHalfMeasure)) = 0 := by
    apply (ENNReal.add_right_inj hpairFinite).1
    calc
      _ = oddPairIntegral f := hadd.symm
      _ = oddPairIntegral (oddFoldAbs f) + 0 := by rw [← hpairEq, add_zero]
  have hgap := (lintegral_eq_zero_iff (measurable_oddAbsGap hf)).1 hzero
  have hproducts : ∀ᵐ p : ℝ × ℝ ∂positiveHalfMeasure.prod positiveHalfMeasure,
      0 ≤ f p.1 * f p.2 := by
    filter_upwards [hgap, positive_quadrant_ae] with p hp hpos
    exact oddAbsGap_le_zero_imp_mul_nonneg f hpos.1 hpos.2 (ENNReal.ofReal_eq_zero.1 hp)
  have hpair : ∀ᵐ x : ℝ ∂positiveHalfMeasure, ∀ᵐ y : ℝ ∂positiveHalfMeasure,
      0 ≤ f x * f y := Measure.ae_ae_of_ae_prod hproducts
  by_cases hzero : f =ᵐ[positiveHalfMeasure] 0
  · left
    filter_upwards [hzero] with x hx
    change 0 ≤ f x
    simpa only [hx, Pi.zero_apply] using (le_refl (0 : ℝ))
  · have hex : ∃ x : ℝ, (∀ᵐ y : ℝ ∂positiveHalfMeasure, 0 ≤ f x * f y) ∧ f x ≠ 0 := by
      by_contra hnot
      apply hzero
      filter_upwards [hpair] with x hx
      change f x = 0
      by_contra hfx
      exact hnot ⟨x, hx, hfx⟩
    obtain ⟨x, hx, hfx⟩ := hex
    rcases lt_or_gt_of_ne hfx with hneg | hpos
    · right
      filter_upwards [hx] with y hy
      change f y ≤ 0
      exact nonpos_of_mul_nonneg_right hy hneg
    · left
      filter_upwards [hx] with y hy
      change 0 ≤ f y
      exact nonneg_of_mul_nonneg_right hy hpos

/-- Equality in the actual Fourier odd-fold contraction forces a single
positive-half a.e. sign for every member of the original odd form domain. -/
theorem energy_oddFoldAbs_eq_imp_sign {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f)
    (heq : energy (oddFoldAbs f) (oddFoldAbs f) = energy f f) :
    0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f ∨ f ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  let m := hf.1.1.mk f
  let g : ℝ → ℝ := fun x => (m x - m (-x)) / 2
  have hm : Measurable m := hf.1.1.stronglyMeasurable_mk.measurable
  have hfm : f =ᵐ[volume] m := hf.1.1.ae_eq_mk
  have hreflection := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hfm
  have hfg : f =ᵐ[volume] g := by
    filter_upwards [hfm, hreflection] with x hx hnx
    change f x = (m x - m (-x)) / 2
    rw [← hx, ← hnx, hodd x]
    ring
  have hg : Measurable g := (hm.sub (hm.comp measurable_neg)).div_const 2
  have hgodd : Function.Odd g := by
    intro x
    dsimp only [g]
    simp only [neg_neg]
    ring
  have hgform := hf.congr_ae hfg
  have hfoldfg : oddFoldAbs f =ᵐ[volume] oddFoldAbs g := by
    filter_upwards [hfg] with x hx
    simp only [oddFoldAbs, oddFoldComp]
    rw [hx]
  have hGeq : gagliardoEnergy (oddFoldAbs g) = gagliardoEnergy g := by
    rw [← gagliardoEnergy_congr_ae hfoldfg, ← gagliardoEnergy_congr_ae hfg,
      (hf.oddFoldAbs hodd).gagliardoEnergy, hf.gagliardoEnergy, heq]
  have hfinite : gagliardoEnergy g ≠ ∞ := by rw [hgform.gagliardoEnergy]; exact ENNReal.ofReal_ne_top
  rcases ae_half_sign_of_gagliardo_oddFoldAbs_eq hg hgodd hfinite hGeq with hpos | hneg
  · left
    filter_upwards [ae_restrict_of_ae hfg, hpos] with x hx hs
    change 0 ≤ f x
    rw [hx]
    exact hs
  · right
    filter_upwards [ae_restrict_of_ae hfg, hneg] with x hx hs
    change f x ≤ 0
    rw [hx]
    exact hs

/-- Actual positive-half sign changes strictly decrease the original
Fourier energy under odd folded absolute value. -/
theorem energy_oddFoldAbs_lt_of_half_sign_changes {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hodd : Function.Odd f)
    (hpos : ¬ 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f)
    (hneg : ¬ f ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] 0) :
    energy (oddFoldAbs f) (oddFoldAbs f) < energy f f := by
  apply lt_of_le_of_ne (energy_oddFoldAbs_le hf hodd)
  intro heq
  rcases energy_oddFoldAbs_eq_imp_sign hf hodd heq with hp | hn
  · exact hpos hp
  · exact hneg hn

end Torsion.Spectral

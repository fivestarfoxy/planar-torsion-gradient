module

public import Torsion.RestrictedSpectralOddGroundSign
public import Torsion.RestrictedSpectralOddGapBounds
public import Torsion.RestrictedSpectralPositiveSets

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Quantitative perturbation bounds for strict positive-half positivity

The actual weak eigenfunction equation cancels the constant and linear
terms in the Rayleigh defect. For a least-odd eigenfunction, folded absolute
value has a gap bounded above by that exact quadratic defect. Combined
with the strictly positive paired kernel this rules out positive-measure
zero sets on the positive half interval.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- Exact quadratic Rayleigh defect under a genuine form-domain
perturbation of an actual weak eigenfunction. -/
theorem IsRestrictedEigenfunction.perturbation_defect {a : ℝ} {f ψ : ℝ → ℝ}
    (hf : IsRestrictedEigenfunction a f) (hψ : MemRestrictedFormDomain ψ) (t : ℝ) :
    energy (fun x => f x - t * ψ x) (fun x => f x - t * ψ x) -
        a * (∫ x : ℝ, (f x - t * ψ x) ^ 2) =
      t ^ 2 * (energy ψ ψ - a * (∫ x : ℝ, ψ x ^ 2)) := by
  have hEu := energy_add_const_mul_self hf.1 hψ (-t)
  have hQu := integral_sq_add_const_mul hf.1 hψ (-t)
  have hself : energy f f = a * ∫ x : ℝ, f x ^ 2 := by
    simpa only [pow_two] using hf.2.2 f hf.1
  have hcross := hf.2.2 ψ hψ
  have heq : (fun x => f x - t * ψ x) = fun x => f x + (-t) * ψ x := by funext x; ring
  simp_rw [sub_eq_add_neg, neg_mul] at *
  rw [hEu, hQu, hself, hcross]
  ring

/-- The actual Fourier energy removed by an odd fold is at most the
quadratic Rayleigh defect of the original perturbation. -/
theorem IsRestrictedEigenfunction.oddFoldAbs_perturbation_gap_le
    {a : ℝ} {f ψ : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hlower : ∀ η : ℝ → ℝ, MemRestrictedFormDomain η → Function.Odd η →
      a * (∫ x : ℝ, η x ^ 2) ≤ energy η η)
    (hψ : MemRestrictedFormDomain ψ) (hψodd : Function.Odd ψ) (t : ℝ) :
    energy (fun x => f x - t * ψ x) (fun x => f x - t * ψ x) -
        energy (oddFoldAbs (fun x => f x - t * ψ x)) (oddFoldAbs (fun x => f x - t * ψ x)) ≤
      t ^ 2 * (energy ψ ψ - a * (∫ x : ℝ, ψ x ^ 2)) := by
  let u : ℝ → ℝ := fun x => f x - t * ψ x
  have hu : MemRestrictedFormDomain u := hf.1.sub (hψ.const_mul t)
  have huodd : Function.Odd u := by intro x; dsimp only [u]; rw [hodd x, hψodd x]; ring
  have hlow := hlower (oddFoldAbs u) (hu.oddFoldAbs huodd) (oddFoldAbs_odd huodd)
  simp only [oddFoldAbs_sq] at hlow
  have hdef := hf.perturbation_defect hψ t
  change energy u u - energy (oddFoldAbs u) (oddFoldAbs u) ≤ _
  change energy u u - a * (∫ x : ℝ, u x ^ 2) = _ at hdef
  linarith

/-- The actual paired-kernel perturbation gap has an explicit O(t²)
upper bound, proved from the original weak equation and odd minimum. -/
theorem IsRestrictedEigenfunction.oddGap_integral_perturbation_le
    {a : ℝ} {f ψ : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hlower : ∀ η : ℝ → ℝ, MemRestrictedFormDomain η → Function.Odd η →
      a * (∫ x : ℝ, η x ^ 2) ≤ energy η η)
    (hψ : MemRestrictedFormDomain ψ) (hψodd : Function.Odd ψ)
    (hm : Measurable f) (hψm : Measurable ψ) (t : ℝ) :
    2 * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (oddAbsGap (fun x => f x - t * ψ x) p.1 p.2)
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) ≤
        ENNReal.ofReal (gagliardoSymbolConstant * t ^ 2 * (energy ψ ψ - a * ∫ x : ℝ, ψ x ^ 2)) := by
  let u : ℝ → ℝ := fun x => f x - t * ψ x
  have hu : MemRestrictedFormDomain u := hf.1.sub (hψ.const_mul t)
  have huodd : Function.Odd u := by intro x; dsimp only [u]; rw [hodd x, hψodd x]; ring
  have hum : Measurable u := hm.sub (hψm.const_mul t)
  have hfold := hu.oddFoldAbs huodd
  have hgapNonneg : 0 ≤ energy u u - energy (oddFoldAbs u) (oddFoldAbs u) :=
    sub_nonneg.2 (energy_oddFoldAbs_le hu huodd)
  have hidentity := energy_oddFoldAbs_gap hu huodd hum
  have hbase : ENNReal.ofReal (gagliardoSymbolConstant * energy u u) =
      ENNReal.ofReal (gagliardoSymbolConstant * energy (oddFoldAbs u) (oddFoldAbs u)) +
        ENNReal.ofReal (gagliardoSymbolConstant * (energy u u - energy (oddFoldAbs u) (oddFoldAbs u))) := by
    rw [← ENNReal.ofReal_add (mul_nonneg gagliardoSymbolConstant_pos.le (energy_nonneg _))
      (mul_nonneg gagliardoSymbolConstant_pos.le hgapNonneg)]
    congr 1
    ring
  have hIeq : 2 * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (oddAbsGap u p.1 p.2)
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) =
      ENNReal.ofReal (gagliardoSymbolConstant * (energy u u - energy (oddFoldAbs u) (oddFoldAbs u))) := by
    apply (ENNReal.add_right_inj ENNReal.ofReal_ne_top).1
    exact hidentity.symm.trans hbase
  change 2 * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (oddAbsGap u p.1 p.2)
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) ≤ _
  rw [hIeq]
  apply ENNReal.ofReal_le_ofReal
  have hbound := mul_le_mul_of_nonneg_left
    (hf.oddFoldAbs_perturbation_gap_le hodd hlower hψ hψodd t) gagliardoSymbolConstant_pos.le
  simpa only [mul_assoc] using hbound


/-- Integrating the pointwise paired-kernel lower bound on a genuine
positive-half rectangle gives a linear lower bound for the actual gap. -/
theorem oddGap_integral_perturbation_rectangle_lower_bound
    {f ψ : ℝ → ℝ} {A B : Set ℝ} {r R δ η t : ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hr : 0 < r) (hAsub : A ⊆ Icc r R) (hBsub : B ⊆ Icc r R)
    (hδ : 0 < δ) (hη : 0 < η) (ht : 0 < t)
    (hAzero : ∀ x ∈ A, f x = 0) (hAψ : ∀ x ∈ A, δ ≤ ψ x)
    (hBf : ∀ x ∈ B, η ≤ f x) (hBψ : ∀ x ∈ B, |ψ x| ≤ 1)
    (htsmall : t ≤ η / 2) :
    ENNReal.ofReal ((2 * δ * η * (r ^ 2 / R ^ 4)) * t) *
        (volume A * volume B) ≤
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (oddAbsGap (fun x => f x - t * ψ x) p.1 p.2)
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hApos : A ⊆ Ioi 0 := fun x hx => hr.trans_le (hAsub hx).1
  have hBpos : B ⊆ Ioi 0 := fun x hx => hr.trans_le (hBsub hx).1
  have hAm : μ A = volume A := by
    rw [show μ = volume.restrict (Ioi (0 : ℝ)) from rfl,
      Measure.restrict_apply hA, inter_eq_left.2 hApos]
  have hBm : μ B = volume B := by
    rw [show μ = volume.restrict (Ioi (0 : ℝ)) from rfl,
      Measure.restrict_apply hB, inter_eq_left.2 hBpos]
  calc
    _ = ∫⁻ p : ℝ × ℝ,
        (A ×ˢ B).indicator (fun _ => ENNReal.ofReal ((2 * δ * η * (r ^ 2 / R ^ 4)) * t)) p
          ∂(μ.prod μ) := by
      rw [lintegral_indicator_const (hA.prod hB), Measure.prod_prod, hAm, hBm]
    _ ≤ _ := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ A ×ˢ B
      · rw [indicator_of_mem hp]
        apply ENNReal.ofReal_le_ofReal
        have hne : p.1 ≠ p.2 := by
          intro heq
          have hz := hAzero p.1 hp.1
          have hb := hBf p.2 hp.2
          rw [heq] at hz
          linarith
        exact oddAbsGap_perturbation_lower_bound hr (hAsub hp.1) (hBsub hp.2) hne
          hδ hη ht (hAzero p.1 hp.1) (hAψ p.1 hp.1) (hBf p.2 hp.2)
          (hBψ p.2 hp.2) (by simpa using htsmall)
      · rw [indicator_of_notMem hp]
        exact bot_le


/-- A genuine linear lower bound cannot be dominated by a quadratic
upper bound for every sufficiently small positive perturbation. -/
theorem nonpos_of_linear_le_quadratic {K D η : ℝ} (hη : 0 < η)
    (hbound : ∀ t : ℝ, 0 < t → t ≤ η / 2 → K * t ≤ D * t ^ 2) : K ≤ 0 := by
  by_contra hK
  have hK : 0 < K := lt_of_not_ge hK
  let t : ℝ := min (η / 4) (K / (2 * (|D| + 1)))
  have hden : 0 < 2 * (|D| + 1) := by positivity
  have ht : 0 < t := lt_min (by positivity) (div_pos hK hden)
  have htη : t ≤ η / 2 := (min_le_left _ _).trans (by linarith)
  have htK : t * (2 * (|D| + 1)) ≤ K :=
    (le_div_iff₀ hden).1 (min_le_right _ _)
  have hmain := hbound t ht htη
  have hdiv : K ≤ D * t := by nlinarith
  have hD : D * t ≤ |D| * t := mul_le_mul_of_nonneg_right (le_abs_self D) ht.le
  nlinarith

/-- An odd Rayleigh minimizer cannot have a non-null zero set opposite
a non-null uniformly positive set on a compact positive rectangle. This
is the irreducibility step, proved quantitatively from the real kernel. -/
theorem IsRestrictedEigenfunction.zero_or_positive_rectangle_null
    {a : ℝ} {f ψ : ℝ → ℝ} {A B : Set ℝ} {r R δ η : ℝ}
    (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hlower : ∀ v : ℝ → ℝ, MemRestrictedFormDomain v → Function.Odd v →
      a * (∫ x : ℝ, v x ^ 2) ≤ energy v v)
    (hm : Measurable f) (hψ : MemRestrictedFormDomain ψ)
    (hψodd : Function.Odd ψ) (hψm : Measurable ψ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hr : 0 < r) (hAsub : A ⊆ Icc r R) (hBsub : B ⊆ Icc r R)
    (hδ : 0 < δ) (hη : 0 < η)
    (hAzero : ∀ x ∈ A, f x = 0) (hAψ : ∀ x ∈ A, δ ≤ ψ x)
    (hBf : ∀ x ∈ B, η ≤ f x) (hBψ : ∀ x ∈ B, |ψ x| ≤ 1) :
    volume A = 0 ∨ volume B = 0 := by
  by_contra hab
  push Not at hab
  have hAfinite : volume A ≠ (∞ : ℝ≥0∞) := (lt_of_le_of_lt (measure_mono hAsub) (measure_Icc_lt_top)).ne
  have hBfinite : volume B ≠ (∞ : ℝ≥0∞) := (lt_of_le_of_lt (measure_mono hBsub) (measure_Icc_lt_top)).ne
  have hAm : 0 < (volume A).toReal := ENNReal.toReal_pos hab.1 hAfinite
  have hBm : 0 < (volume B).toReal := ENNReal.toReal_pos hab.2 hBfinite
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.2 (by
    intro he; exact hab.1 (by rw [he, measure_empty]))
  obtain ⟨x, hx⟩ := hAne
  have hR : 0 < R := hr.trans_le ((hAsub hx).1.trans (hAsub hx).2)
  let c : ℝ := 2 * δ * η * (r ^ 2 / R ^ 4)
  have hc : 0 < c := by dsimp only [c]; positivity
  let D : ℝ := gagliardoSymbolConstant * (energy ψ ψ - a * ∫ x : ℝ, ψ x ^ 2)
  have hD : 0 ≤ D := mul_nonneg gagliardoSymbolConstant_pos.le (sub_nonneg.2 (hlower ψ hψ hψodd))
  have hcoeff := nonpos_of_linear_le_quadratic (K := 2 * c * (volume A).toReal * (volume B).toReal)
      (D := D) hη (by
    intro t ht htsmall
    have hlow := oddGap_integral_perturbation_rectangle_lower_bound hA hB hr hAsub hBsub
      hδ hη ht hAzero hAψ hBf hBψ htsmall
    have hup := hf.oddGap_integral_perturbation_le hodd hlower hψ hψodd hm hψm t
    have htotal := (mul_le_mul_right hlow (2 : ℝ≥0∞)).trans hup
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htotal
    have hrhs : 0 ≤ gagliardoSymbolConstant * t ^ 2 *
        (energy ψ ψ - a * ∫ x : ℝ, ψ x ^ 2) := by
      have he := sub_nonneg.2 (hlower ψ hψ hψodd)
      exact mul_nonneg (mul_nonneg gagliardoSymbolConstant_pos.le (sq_nonneg t)) he
    have hct : 0 ≤ 2 * δ * η * (r ^ 2 / R ^ 4) * t := (mul_pos hc ht).le
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hreal
    rw [ENNReal.toReal_ofReal hct, ENNReal.toReal_ofReal hrhs] at hreal
    dsimp only [c] at *
    dsimp only [D]
    nlinarith [hreal])
  have hpositive : 0 < 2 * c * (volume A).toReal * (volume B).toReal := by positivity
  exact (not_le_of_gt hpositive) hcoeff


/-- Every measurable actual least-odd eigenfunction of nonnegative
positive-half sign is strictly positive almost everywhere on (0,1).
The proof uses genuine smooth odd tests and a quantitative folding gap. -/
theorem IsRestrictedEigenfunction.pos_ae_of_odd_rayleigh_lower_bound_of_measurable
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hlower : ∀ v : ℝ → ℝ, MemRestrictedFormDomain v → Function.Odd v →
      a * (∫ x : ℝ, v x ^ 2) ≤ energy v v)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f) (hm : Measurable f) :
    ∀ᵐ x : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < f x := by
  let Z : Set ℝ := {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ f x = 0}
  have hZ : MeasurableSet Z := measurableSet_Ioo.inter (measurableSet_eq_fun hm measurable_const)
  have hZzero : volume Z = 0 := by
    by_contra hZne
    obtain ⟨η, hη, hPne⟩ := hf.exists_positive_half_level hodd hnonneg
    let P : Set ℝ := {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ η ≤ f x}
    have hP : MeasurableSet P := measurableSet_Ioo.inter (measurableSet_le measurable_const hm)
    obtain ⟨r, R, hr, hR0, hR1, hZc, hPc⟩ :=
      exists_common_positive_compact_interval_inter_measure_ne_zero
        (show Z ⊆ Ioo (0 : ℝ) 1 from fun _ hx => hx.1) hZne
        (show P ⊆ Ioo (0 : ℝ) 1 from fun _ hx => hx.1) hPne
    let ψ : ℝ → ℝ := oddPlateauTest R hR0 hR1
    have hψcore : IsCore ψ := oddPlateauTest_isCore R hR0 hR1
    have hnull := hf.zero_or_positive_rectangle_null hodd hlower hm
      hψcore.memRestrictedFormDomain (oddPlateauTest_odd R hR0 hR1)
      hψcore.1.continuous.measurable (hZ.inter measurableSet_Icc) (hP.inter measurableSet_Icc)
      hr (fun _ hx => hx.2) (fun _ hx => hx.2) hr hη
      (fun _ hx => hx.1.2)
      (fun _ hx => (oddPlateauTest_rectangle_bounds R hR0 hR1 hr hx.2).1)
      (fun _ hx => hx.1.2)
      (fun x _ => oddPlateauTest_abs_le_one R hR0 hR1 x)
    exact hnull.elim hZc hPc
  have hnotzero : ∀ᵐ x : ℝ ∂volume, ¬ x ∈ Z := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hZzero
  have hnonnegI : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f :=
    ae_restrict_of_ae_restrict_of_subset (fun _ hx => hx.1) hnonneg
  filter_upwards [ae_restrict_of_ae hnotzero, hnonnegI,
    ae_restrict_mem measurableSet_Ioo] with x hx hn hxi
  exact lt_of_le_of_ne hn (Ne.symm (fun hz => hx ⟨hxi, hz⟩))

/-- Strict a.e. positivity for the original form-domain representative.
No continuity, pointwise regularity, or strong maximum principle is
assumed: the proof constructs a measurable odd representative and uses
the actual variational minimum and paired-kernel irreducibility. -/
theorem IsRestrictedEigenfunction.pos_ae_of_odd_rayleigh_lower_bound
    {a : ℝ} {f : ℝ → ℝ} (hf : IsRestrictedEigenfunction a f) (hodd : Function.Odd f)
    (hlower : ∀ v : ℝ → ℝ, MemRestrictedFormDomain v → Function.Odd v →
      a * (∫ x : ℝ, v x ^ 2) ≤ energy v v)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f) :
    ∀ᵐ x : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < f x := by
  let m := hf.1.1.aestronglyMeasurable.mk f
  let g : ℝ → ℝ := fun x => (m x - m (-x)) / 2
  have hm : Measurable m := hf.1.1.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfm : f =ᵐ[volume] m := hf.1.1.aestronglyMeasurable.ae_eq_mk
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
  have hgnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] g := by
    filter_upwards [ae_restrict_of_ae hfg, hnonneg] with x hx hn
    change 0 ≤ g x
    rw [← hx]
    exact hn
  have hgpos := (hf.congr_ae hfg).pos_ae_of_odd_rayleigh_lower_bound_of_measurable
    hgodd hlower hgnonneg hg
  filter_upwards [ae_restrict_of_ae hfg, hgpos] with x hx hp
  rw [hx]
  exact hp

end Torsion.Spectral

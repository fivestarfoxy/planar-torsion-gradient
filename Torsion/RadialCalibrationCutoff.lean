import Torsion.MarkedFluxExhaustion
import Torsion.Calibration
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Lattice

/-!
# Concrete endpoint passage for radial calibration

The cutoffs below vanish on actual endpoint neighborhoods and eventually
equal one at every interior angle. The lower profiles give increasing open
marked domains whose union is the original radial domain. Thus their actual
weak torsion fluxes converge, without an assumed flux-limit certificate.

The final theorem transfers a calibration known for compactly supported
continuous perturbations to every positive continuous radial profile. The
compact-perturbation inequality (ultimately a shape-calculus obligation)
remains explicit; no stationarity-to-global-inequality implication is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Torsion.RadialCalibration

/-- Continuous cutoff with a genuine zero neighborhood at each endpoint. -/
def endpointCutoff (n : ℕ) (θ : ℝ) : ℝ :=
  min 1 (max 0 (((n : ℝ) + 1) * min θ (Real.pi - θ) - 1))

theorem endpointCutoff_continuous (n : ℕ) : Continuous (endpointCutoff n) := by
  unfold endpointCutoff
  fun_prop

theorem endpointCutoff_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ endpointCutoff n θ :=
  le_min (by norm_num) (le_max_left _ _)

theorem endpointCutoff_le_one (n : ℕ) (θ : ℝ) : endpointCutoff n θ ≤ 1 :=
  min_le_left _ _

theorem endpointCutoff_mono {θ : ℝ} (hθ : θ ∈ Icc 0 Real.pi) :
    Monotone (fun n => endpointCutoff n θ) := by
  intro m n hmn
  apply min_le_min le_rfl
  apply max_le_max le_rfl
  have hd : 0 ≤ min θ (Real.pi - θ) := le_min hθ.1 (sub_nonneg.2 hθ.2)
  have hn : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  nlinarith

/-- Each interior angle eventually lies in the region where the cutoff is one. -/
theorem endpointCutoff_eventually_one {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    ∀ᶠ n in atTop, endpointCutoff n θ = 1 := by
  have hd : 0 < min θ (Real.pi - θ) := lt_min hθ.1 (sub_pos.2 hθ.2)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / min θ (Real.pi - θ))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hN' : 2 < (N : ℝ) * min θ (Real.pi - θ) := (div_lt_iff₀ hd).mp hN
  have hn' : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hlarge : 1 ≤ ((n : ℝ) + 1) * min θ (Real.pi - θ) - 1 := by
    nlinarith
  exact min_eq_left ((le_max_right _ _).trans' hlarge)

theorem endpointCutoff_tendsto_one {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    Tendsto (fun n => endpointCutoff n θ) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' ((endpointCutoff_eventually_one hθ).mono fun _ h => h.symm)

/-- The explicit common width of the two zero neighborhoods. -/
theorem endpointCutoff_zero_near_endpoints (n : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ Icc 0 Real.pi,
      (θ ≤ ε ∨ Real.pi - ε ≤ θ) → endpointCutoff n θ = 0 := by
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
  intro θ hθ hnear
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hd : min θ (Real.pi - θ) ≤ 1 / ((n : ℝ) + 1) := by
    rcases hnear with hnear | hnear
    · exact (min_le_left _ _).trans hnear
    · exact (min_le_right _ _).trans (by linarith)
  have hsmall : ((n : ℝ) + 1) * min θ (Real.pi - θ) - 1 ≤ 0 := by
    have := (le_div_iff₀ hn).mp hd
    nlinarith
  simp only [endpointCutoff, max_eq_left hsmall]
  norm_num

/-- Compact endpoint-preserving perturbation of the reference radius. -/
def cutoffProfile (R₀ R : ℝ → ℝ) (n : ℕ) (θ : ℝ) : ℝ :=
  R₀ θ + endpointCutoff n θ * (R θ - R₀ θ)

/-- The lower profile is needed because the perturbation can have either sign. -/
def lowerProfile (R₀ R : ℝ → ℝ) (n : ℕ) (θ : ℝ) : ℝ :=
  min (R θ) (cutoffProfile R₀ R n θ)

theorem cutoffProfile_mem_positive {R₀ R : ℝ → ℝ}
    (h₀ : R₀ ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hR : R ∈ RadialFluxConcavity.positiveContinuousProfiles) (n : ℕ) :
    cutoffProfile R₀ R n ∈ RadialFluxConcavity.positiveContinuousProfiles := by
  refine ⟨h₀.1.add ((endpointCutoff_continuous n).continuousOn.mul (hR.1.sub h₀.1)), ?_⟩
  intro θ hθ
  exact Calibration.cutoff_positive (h₀.2 θ hθ) (hR.2 θ hθ)
    (endpointCutoff_nonneg n θ) (endpointCutoff_le_one n θ)

theorem lowerProfile_mem_positive {R₀ R : ℝ → ℝ}
    (h₀ : R₀ ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hR : R ∈ RadialFluxConcavity.positiveContinuousProfiles) (n : ℕ) :
    lowerProfile R₀ R n ∈ RadialFluxConcavity.positiveContinuousProfiles := by
  have hc := cutoffProfile_mem_positive h₀ hR n
  exact ⟨fun θ hθ => (hR.1 θ hθ).inf (hc.1 θ hθ),
    fun θ hθ => lt_min (hR.2 θ hθ) (hc.2 θ hθ)⟩

theorem lowerProfile_mono {R₀ R : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Icc 0 Real.pi) :
    Monotone (fun n => lowerProfile R₀ R n θ) := by
  intro m n hmn
  exact Calibration.lower_cutoff_mono (endpointCutoff_le_one m θ)
    (endpointCutoff_le_one n θ) (endpointCutoff_mono hθ hmn)

theorem cutoffProfile_eventually_eq {R₀ R : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Ioo 0 Real.pi) :
    ∀ᶠ n in atTop, cutoffProfile R₀ R n θ = R θ := by
  filter_upwards [endpointCutoff_eventually_one hθ] with n hn
  simp [cutoffProfile, hn]

theorem lowerProfile_eventually_eq {R₀ R : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Ioo 0 Real.pi) :
    ∀ᶠ n in atTop, lowerProfile R₀ R n θ = R θ := by
  filter_upwards [cutoffProfile_eventually_eq (R₀ := R₀) (R := R) hθ] with n hn
  simp [lowerProfile, hn]

theorem cutoffProfile_eq_near_endpoints (R₀ R : ℝ → ℝ) (n : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ Icc 0 Real.pi,
      (θ ≤ ε ∨ Real.pi - ε ≤ θ) → cutoffProfile R₀ R n θ = R₀ θ := by
  obtain ⟨ε, hε, hc⟩ := endpointCutoff_zero_near_endpoints n
  exact ⟨ε, hε, fun θ hθ hnear => by simp [cutoffProfile, hc θ hθ hnear]⟩

private theorem radialDomain_mono_on {R S : ℝ → ℝ}
    (hRS : ∀ θ ∈ Ioo 0 Real.pi, R θ ≤ S θ) : radialDomain R ⊆ radialDomain S := by
  rintro z ⟨θ, r, hθ, hθπ, hr, hrR, hz⟩
  exact ⟨θ, r, hθ, hθπ, hr, hrR.trans_le (hRS θ ⟨hθ, hθπ⟩), hz⟩

/-- The dilation sandwich for actual continuous radial weak torsion fluxes. -/
theorem torsionFlux_radial_sandwich {R S : ℝ → ℝ}
    (hR : R ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hS : S ∈ RadialFluxConcavity.positiveContinuousProfiles)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hbelow : ∀ θ ∈ Ioo 0 Real.pi, a * R θ ≤ S θ)
    (habove : ∀ θ ∈ Ioo 0 Real.pi, S θ ≤ b * R θ) :
    a * torsionFlux (radialDomain R) ≤ torsionFlux (radialDomain S) ∧
    torsionFlux (radialDomain S) ≤ b * torsionFlux (radialDomain R) := by
  have hmR := RadialGeometry.radialDomain_isMarked hR.1 hR.2
  have hmS := RadialGeometry.radialDomain_isMarked hS.1 hS.2
  have hmA := RadialGeometry.radialDomain_isMarked (continuousOn_const.mul hR.1)
    (fun θ hθ => mul_pos ha (hR.2 θ hθ))
  have hmB := RadialGeometry.radialDomain_isMarked (continuousOn_const.mul hR.1)
    (fun θ hθ => mul_pos hb (hR.2 θ hθ))
  have hlo := torsionFlux_mono hmA hmS (radialDomain_mono_on hbelow)
  have hhi := torsionFlux_mono hmS hmB (radialDomain_mono_on habove)
  have heqa : torsionFlux (radialDomain (fun θ => a * R θ)) =
      a * torsionFlux (radialDomain R) := by
    change torsionFlux (radialDomain (a • R)) = _
    rw [RadialFluxConcavity.radialDomain_smul R a ha, torsionFlux_dilate hmR a ha]
  have heqb : torsionFlux (radialDomain (fun θ => b * R θ)) =
      b * torsionFlux (radialDomain R) := by
    change torsionFlux (radialDomain (b • R)) = _
    rw [RadialFluxConcavity.radialDomain_smul R b hb, torsionFlux_dilate hmR b hb]
  exact ⟨heqa ▸ hlo, heqb ▸ hhi⟩

/-- Multiplicative uniform radial approximation passes to the actual flux.
No regularity of the competing boundaries is needed. -/
theorem torsionFlux_tendsto_of_radial_sandwich {R : ℝ → ℝ} {S : ℕ → ℝ → ℝ}
    (hR : R ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hS : ∀ n, S n ∈ RadialFluxConcavity.positiveContinuousProfiles)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hε₁ : ∀ n, ε n < 1)
    (hbelow : ∀ n θ, θ ∈ Ioo 0 Real.pi → (1 - ε n) * R θ ≤ S n θ)
    (habove : ∀ n θ, θ ∈ Ioo 0 Real.pi → S n θ ≤ (1 + ε n) * R θ)
    (hε₀ : ∀ n, 0 ≤ ε n) :
    Tendsto (fun n => torsionFlux (radialDomain (S n))) atTop
      (𝓝 (torsionFlux (radialDomain R))) := by
  have hb (n : ℕ) := torsionFlux_radial_sandwich hR (hS n)
    (sub_pos.2 (hε₁ n)) (by have := hε₀ n; linarith)
    (hbelow n) (habove n)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hl := (hone.sub hε).mul_const (torsionFlux (radialDomain R))
  have hu := (hone.add hε).mul_const (torsionFlux (radialDomain R))
  simp only [sub_zero, add_zero, one_mul] at hl hu
  exact hl.squeeze' hu (Eventually.of_forall fun n => (hb n).1)
    (Eventually.of_forall fun n => (hb n).2)

/-- A quantitative uniform-radius error estimate. The lower radius bound
controls flux continuity even for radial domains with irregular boundaries. -/
theorem torsionFlux_radial_error {R S : ℝ → ℝ}
    (hR : R ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hS : S ∈ RadialFluxConcavity.positiveContinuousProfiles)
    {m δ : ℝ} (hm : 0 < m) (hδ : 0 ≤ δ) (hδm : δ < m)
    (hmin : ∀ θ ∈ Icc 0 Real.pi, m ≤ R θ)
    (herr : ∀ θ ∈ Icc 0 Real.pi, |S θ - R θ| ≤ δ) :
    |torsionFlux (radialDomain S) - torsionFlux (radialDomain R)| ≤
      (δ / m) * torsionFlux (radialDomain R) := by
  have he₀ : 0 ≤ δ / m := div_nonneg hδ hm.le
  have he₁ : δ / m < 1 := (div_lt_one hm).2 hδm
  have hbounds (θ : ℝ) (hθ : θ ∈ Ioo 0 Real.pi) :
      (1 - δ / m) * R θ ≤ S θ ∧ S θ ≤ (1 + δ / m) * R θ := by
    have hθ' : θ ∈ Icc 0 Real.pi := ⟨hθ.1.le, hθ.2.le⟩
    have he := abs_le.mp (herr θ hθ')
    have hmul := mul_le_mul_of_nonneg_left (hmin θ hθ') he₀
    have hdm : δ / m * m = δ := div_mul_cancel₀ δ hm.ne'
    rw [hdm] at hmul
    constructor <;> nlinarith
  have hb := torsionFlux_radial_sandwich hR hS (sub_pos.2 he₁)
    (by linarith : 0 < 1 + δ / m) (fun θ hθ => (hbounds θ hθ).1)
    (fun θ hθ => (hbounds θ hθ).2)
  apply abs_le.mpr
  constructor <;> nlinarith [hb.1, hb.2]

/-- Uniform radial convergence implies convergence of the actual marked
flux, by the dilation sandwich and the positive minimum of the limit radius. -/
theorem torsionFlux_tendsto_of_uniform_radial {R : ℝ → ℝ} {S : ℕ → ℝ → ℝ}
    (hR : R ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hS : ∀ n, S n ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hlim : TendstoUniformlyOn S R atTop (Icc 0 Real.pi)) :
    Tendsto (fun n => torsionFlux (radialDomain (S n))) atTop
      (𝓝 (torsionFlux (radialDomain R))) := by
  obtain ⟨θ₀, hθ₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) Real.pi).Nonempty from ⟨0, le_rfl, Real.pi_pos.le⟩) hR.1
  let m := R θ₀
  have hm : 0 < m := hR.2 θ₀ hθ₀
  let q := torsionFlux (radialDomain R)
  have hq : 0 ≤ q := torsionFlux_nonneg (RadialGeometry.radialDomain_isMarked hR.1 hR.2)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := min (1 / 2 : ℝ) (ε / (q + 1))
  have hq₁ : 0 < q + 1 := by linarith
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε hq₁)
  have hη₁ : η < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hηq : η * q < ε := by
    have hb : η * (q + 1) ≤ ε := (le_div_iff₀ hq₁).mp (min_le_right _ _)
    nlinarith
  have hu := Metric.tendstoUniformlyOn_iff.mp hlim (m * η) (mul_pos hm hη)
  filter_upwards [hu] with n hn
  have herr := torsionFlux_radial_error hR (hS n) hm (mul_nonneg hm.le hη.le)
    (by nlinarith : m * η < m) (fun θ hθ => hmin hθ)
    (fun θ hθ => by simpa [Real.dist_eq, abs_sub_comm] using (hn θ hθ).le)
  have hdiv : m * η / m = η := by field_simp [hm.ne']
  rw [hdiv] at herr
  have hh : dist (torsionFlux (radialDomain (S n))) q ≤ η * q := by
    simpa [Real.dist_eq, q] using herr
  exact hh.trans_lt hηq

theorem lowerProfile_domain_monotone (R₀ R : ℝ → ℝ) :
    Monotone (fun n => radialDomain (lowerProfile R₀ R n)) := by
  intro m n hmn
  exact radialDomain_mono_on fun θ hθ => lowerProfile_mono ⟨hθ.1.le, hθ.2.le⟩ hmn

/-- The actual union, including all interior angles, is the competing domain. -/
theorem iUnion_lowerProfile_domain (R₀ R : ℝ → ℝ) :
    (⋃ n, radialDomain (lowerProfile R₀ R n)) = radialDomain R := by
  apply Subset.antisymm
  · refine iUnion_subset fun n => radialDomain_mono_on ?_
    intro θ _
    exact min_le_left _ _
  · rintro z ⟨θ, r, hθ, hθπ, hr, hrR, hz⟩
    obtain ⟨n, hn⟩ := (lowerProfile_eventually_eq (R₀ := R₀) (R := R)
      ⟨hθ, hθπ⟩).exists
    exact mem_iUnion.mpr ⟨n, θ, r, hθ, hθπ, hr, hn.symm ▸ hrR, hz⟩

/-- Endpoint exhaustion converges for the constructed weak torsion flux itself. -/
theorem torsionFlux_lowerProfile_tendsto {R₀ R : ℝ → ℝ}
    (h₀ : R₀ ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hR : R ∈ RadialFluxConcavity.positiveContinuousProfiles) :
    Tendsto (fun n => torsionFlux (radialDomain (lowerProfile R₀ R n))) atTop
      (𝓝 (torsionFlux (radialDomain R))) := by
  have hm (n : ℕ) := lowerProfile_mem_positive h₀ hR n
  have hU := RadialGeometry.radialDomain_isMarked hR.1 hR.2
  rw [← iUnion_lowerProfile_domain R₀ R] at hU ⊢
  exact torsionFlux_tendsto_of_exhaustion (lowerProfile_domain_monotone R₀ R)
    (fun n => RadialGeometry.radialDomain_isMarked (hm n).1 (hm n).2) hU

/-- Dominated convergence for the actual angular calibration integrals. -/
theorem integral_cutoffProfile_tendsto {R₀ R γ : ℝ → ℝ}
    (h₀ : ContinuousOn R₀ (Icc 0 Real.pi))
    (hR : ContinuousOn R (Icc 0 Real.pi))
    (hγ : ContinuousOn γ (Icc 0 Real.pi)) :
    Tendsto (fun n => ∫ θ in Ioo 0 Real.pi, γ θ * cutoffProfile R₀ R n θ)
      atTop (𝓝 (∫ θ in Ioo 0 Real.pi, γ θ * R θ)) := by
  have hc (n : ℕ) : ContinuousOn (cutoffProfile R₀ R n) (Icc 0 Real.pi) :=
    h₀.add ((endpointCutoff_continuous n).continuousOn.mul (hR.sub h₀))
  have hb : IntegrableOn (fun θ => |γ θ| * (|R₀ θ| + |R θ|)) (Ioo 0 Real.pi) :=
    ((hγ.abs.mul (h₀.abs.add hR.abs)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  apply tendsto_integral_of_dominated_convergence (fun θ => |γ θ| * (|R₀ θ| + |R θ|))
    (fun n => ((hγ.mul (hc n)).mono Ioo_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioo) hb
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hχ₀ := endpointCutoff_nonneg n θ
    have hχ₁ := endpointCutoff_le_one n θ
    have heq : cutoffProfile R₀ R n θ =
        (1 - endpointCutoff n θ) * R₀ θ + endpointCutoff n θ * R θ := by
      unfold cutoffProfile
      ring
    rw [heq]
    calc
      _ ≤ |(1 - endpointCutoff n θ) * R₀ θ| + |endpointCutoff n θ * R θ| :=
        abs_add_le _ _
      _ = (1 - endpointCutoff n θ) * |R₀ θ| + endpointCutoff n θ * |R θ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.2 hχ₁), abs_of_nonneg hχ₀]
      _ ≤ |R₀ θ| + |R θ| := by
        have h0 := abs_nonneg (R₀ θ)
        have h1 := abs_nonneg (R θ)
        nlinarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hlim : Tendsto (fun n => cutoffProfile R₀ R n θ) atTop (𝓝 (R θ)) :=
      tendsto_const_nhds.congr' ((cutoffProfile_eventually_eq hθ).mono fun _ h => h.symm)
    exact tendsto_const_nhds.mul hlim

/-- Full endpoint passage for the constructed marked torsion flux. The only
calibration premise concerns perturbations agreeing with the reference on
actual endpoint neighborhoods. Their convergence and all domain/flux limits
are proved here, for arbitrary positive continuous competitors. -/
theorem calibration_of_compact_perturbations {R₀ R γ : ℝ → ℝ}
    (h₀ : R₀ ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hR : R ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hγ : ContinuousOn γ (Icc 0 Real.pi))
    (hcompact : ∀ S ∈ RadialFluxConcavity.positiveContinuousProfiles,
      (∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ Icc 0 Real.pi,
        (θ ≤ ε ∨ Real.pi - ε ≤ θ) → S θ = R₀ θ) →
      torsionFlux (radialDomain S) ≤ ∫ θ in Ioo 0 Real.pi, γ θ * S θ) :
    torsionFlux (radialDomain R) ≤ ∫ θ in Ioo 0 Real.pi, γ θ * R θ := by
  apply Calibration.calibration_of_cutoff
    (fun S => torsionFlux (radialDomain S))
    (fun S => ∫ θ in Ioo 0 Real.pi, γ θ * S θ) R
    (lowerProfile R₀ R) (cutoffProfile R₀ R)
  · intro n
    have hl := lowerProfile_mem_positive h₀ hR n
    have hc := cutoffProfile_mem_positive h₀ hR n
    exact torsionFlux_mono (RadialGeometry.radialDomain_isMarked hl.1 hl.2)
      (RadialGeometry.radialDomain_isMarked hc.1 hc.2)
      (radialDomain_mono_on fun _ _ => min_le_right _ _)
  · intro n
    exact hcompact _ (cutoffProfile_mem_positive h₀ hR n)
      (cutoffProfile_eq_near_endpoints R₀ R n)
  · exact torsionFlux_lowerProfile_tendsto h₀ hR
  · exact integral_cutoffProfile_tendsto h₀.1 hR.1 hγ

/-- Concavity and a localized right shape derivative suffice for the full
radial supporting inequality. This isolates the actual remaining localized
Hadamard obligation: every endpoint and exhaustion limit is discharged. -/
theorem calibration_of_local_derivative {R₀ R γ : ℝ → ℝ}
    (h₀ : R₀ ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hR : R ∈ RadialFluxConcavity.positiveContinuousProfiles)
    (hγ : ContinuousOn γ (Icc 0 Real.pi))
    (heuler : torsionFlux (radialDomain R₀) = ∫ θ in Ioo 0 Real.pi, γ θ * R₀ θ)
    (hlocal : ∀ S ∈ RadialFluxConcavity.positiveContinuousProfiles,
      (∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ Icc 0 Real.pi,
        (θ ≤ ε ∨ Real.pi - ε ≤ θ) → S θ = R₀ θ) →
      HasDerivWithinAt (fun t : ℝ => torsionFlux
        (radialDomain (AffineMap.lineMap R₀ S t)))
        (∫ θ in Ioo 0 Real.pi, γ θ * (S θ - R₀ θ)) (Ioi 0) 0) :
    torsionFlux (radialDomain R) ≤ ∫ θ in Ioo 0 Real.pi, γ θ * R θ := by
  apply calibration_of_compact_perturbations h₀ hR hγ
  intro S hS hnear
  have ht := Calibration.tangent_bound torsionFlux_radial_concaveOn h₀ hS
    (hlocal S hS hnear)
  have hiS : IntegrableOn (fun θ => γ θ * S θ) (Ioo 0 Real.pi) :=
    ((hγ.mul hS.1).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hi₀ : IntegrableOn (fun θ => γ θ * R₀ θ) (Ioo 0 Real.pi) :=
    ((hγ.mul h₀.1).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hid : (∫ θ in Ioo 0 Real.pi, γ θ * (S θ - R₀ θ)) =
      (∫ θ in Ioo 0 Real.pi, γ θ * S θ) -
        ∫ θ in Ioo 0 Real.pi, γ θ * R₀ θ := by
    simp_rw [mul_sub]
    exact integral_sub hiS hi₀
  rw [heuler, hid] at ht
  linarith

end Torsion.RadialCalibration

module

public import Torsion.RestrictedSpectralEnergyContinuity
public import Torsion.FourierHilbertPairing
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fourier continuity and closedness on the actual restricted support

L² representatives supported almost everywhere in `(-1,1)` are actual L¹
functions. On this fixed support, L² convergence implies L¹ convergence
and uniform convergence of the original Fourier integrals. These results
identify limits of the actual weighted Fourier graph, rather than assuming
a closed operator in place of the original integral definition.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- Restricted-support L² representatives are genuinely integrable. -/
theorem integrable_of_memLp_two_zero_exterior {f : ℝ → ℝ}
    (hf : MemLp f 2 volume)
    (hzero : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x = 0) : Integrable f := by
  have hi : IntegrableOn f (Ioo (-1 : ℝ) 1) :=
    MemLp.integrable (by norm_num) (hf.restrict _)
  have hI : Integrable ((Ioo (-1 : ℝ) 1).indicator f) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hi
  apply hI.congr
  filter_upwards [hzero] with x hx
  by_cases hmem : x ∈ Ioo (-1 : ℝ) 1
  · simp [hmem]
  · simp [hmem, hx hmem]

/-- Norms of an actual zero-exterior representative equal its restricted
norms on the interval, for every exponent. -/
theorem eLpNorm_eq_restrict_of_zero_exterior {f : ℝ → ℝ}
    (hzero : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x = 0) (p : ℝ≥0∞) :
    eLpNorm f p volume = eLpNorm f p (volume.restrict (Ioo (-1 : ℝ) 1)) := by
  have heq : f =ᵐ[volume] (Ioo (-1 : ℝ) 1).indicator f := by
    filter_upwards [hzero] with x hx
    by_cases hmem : x ∈ Ioo (-1 : ℝ) 1
    · simp [hmem]
    · simp [hmem, hx hmem]
  rw [eLpNorm_congr_ae heq, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo]

/-- The fixed interval gives a genuine L²-to-L¹ norm estimate. -/
theorem eLpNorm_one_le_two_of_zero_exterior {f : ℝ → ℝ}
    (hf : MemLp f 2 volume)
    (hzero : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x = 0) :
    eLpNorm f 1 volume ≤ eLpNorm f 2 volume * (2 : ℝ≥0∞) ^ (1 - 1 / (2 : ℝ)) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (Ioo (-1 : ℝ) 1))
    (p := 1) (q := 2) (by norm_num) (hf.restrict _).1
  rw [← eLpNorm_eq_restrict_of_zero_exterior hzero 1,
    ← eLpNorm_eq_restrict_of_zero_exterior hzero 2] at h
  simpa only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one, Measure.restrict_apply_univ,
    Real.volume_Ioo, show (1 - (-1 : ℝ)) = 2 by norm_num, ENNReal.ofReal_ofNat] using h

/-- L² convergence on the common restricted support is actual L¹
convergence, stated in the original seminorms. -/
theorem tendsto_eLpNorm_one_of_two_zero_exterior
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hv : ∀ n, MemLp (v n) 2 volume) (hf : MemLp f 2 volume)
    (hvzero : ∀ n, ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0)
    (hfzero : ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x = 0)
    (hlim : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => v n x - f x) 1 volume) atTop (𝓝 0) := by
  have hconst : (2 : ℝ≥0∞) ^ (1 - 1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num)
  have hupper := ENNReal.Tendsto.mul_const hlim (Or.inr hconst)
  simp only [zero_mul] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le _)
  intro n
  apply eLpNorm_one_le_two_of_zero_exterior ((hv n).sub hf)
  filter_upwards [hvzero n, hfzero] with x hx hy hout
  simp [hx hout, hy hout]

/-- The zero exterior condition is preserved by actual L² convergence.
The proof uses an a.e. convergent subsequence of the original values. -/
theorem zero_exterior_of_tendsto_eLpNorm_two
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hv : ∀ n, MemLp (v n) 2 volume) (hf : MemLp f 2 volume)
    (hvzero : ∀ n, ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0)
    (hlim : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0)) :
    ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x = 0 := by
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun n => (hv n).1) hf.1 hlim
  obtain ⟨ns, _, hns⟩ := hmeasure.exists_seq_tendsto_ae
  filter_upwards [hns, ae_all_iff.2 hvzero] with x hx hzero hout
  have heq : (fun n => v (ns n) x) = fun _ => (0 : ℝ) :=
    funext fun n => hzero (ns n) hout
  have hz : Tendsto (fun n => v (ns n) x) atTop (𝓝 0) := by
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hx hz

/-- Uniform control of the actual Fourier difference by the actual L¹
difference; no Fourier L² extension is substituted here. -/
theorem norm_fourier_sub_le_integral_norm {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    ‖fourier f ξ - fourier g ξ‖ ≤ ∫ x : ℝ, ‖f x - g x‖ := by
  have heq := congrFun (fourier_sub hf hg) ξ
  change fourier (fun x => f x - g x) ξ = fourier f ξ - fourier g ξ at heq
  rw [← heq]
  exact norm_fourier_le_integral_norm _ ξ

/-- Actual L¹ convergence gives uniform convergence of the original
Fourier integrals, without a common-support hypothesis. -/
theorem tendstoUniformly_fourier_of_tendsto_eLpNorm_one
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hv : ∀ n, Integrable (v n)) (hf : Integrable f)
    (hlim : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 1 volume) atTop (𝓝 0)) :
    TendstoUniformly (fun n => fourier (v n)) (fourier f) atTop := by
  have hreal : Tendsto (fun n => ∫ x : ℝ, ‖v n x - f x‖) atTop (𝓝 0) := by
    have htoReal := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hlim
    have heq (n : ℕ) : (∫ x : ℝ, ‖v n x - f x‖) =
        (eLpNorm (fun x => v n x - f x) 1 volume).toReal := by
      simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using
        integral_norm_eq_lintegral_enorm ((hv n).aestronglyMeasurable.sub hf.aestronglyMeasurable)
    simp_rw [heq]
    exact htoReal
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  filter_upwards [hreal.eventually (eventually_lt_nhds hε)] with n hn ξ
  rw [dist_comm, dist_eq_norm]
  exact (norm_fourier_sub_le_integral_norm (hv n) hf ξ).trans_lt hn

/-- Common-support L² convergence implies uniform convergence on the entire
frequency line of the actual Fourier integrals. -/
theorem tendstoUniformly_fourier_of_tendsto_eLpNorm_two
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hv : ∀ n, MemLp (v n) 2 volume) (hf : MemLp f 2 volume)
    (hvzero : ∀ n, ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0)
    (hlim : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0)) :
    TendstoUniformly (fun n => fourier (v n)) (fourier f) atTop := by
  have hfzero := zero_exterior_of_tendsto_eLpNorm_two hv hf hvzero hlim
  have hL1 := tendsto_eLpNorm_one_of_two_zero_exterior hv hf hvzero hfzero hlim
  have hreal : Tendsto (fun n => ∫ x : ℝ, ‖v n x - f x‖) atTop (𝓝 0) := by
    have htoReal := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hL1
    have heq (n : ℕ) : (∫ x : ℝ, ‖v n x - f x‖) =
        (eLpNorm (fun x => v n x - f x) 1 volume).toReal := by
      simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using
        integral_norm_eq_lintegral_enorm ((hv n).1.sub hf.1)
    simp_rw [heq]
    exact htoReal
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  filter_upwards [hreal.eventually (eventually_lt_nhds hε)] with n hn ξ
  rw [dist_comm, dist_eq_norm]
  exact (norm_fourier_sub_le_integral_norm
    (integrable_of_memLp_two_zero_exterior (hv n) (hvzero n))
    (integrable_of_memLp_two_zero_exterior hf hfzero) ξ).trans_lt hn

/-- Pointwise convergence of the original weighted Fourier integrals,
without any a priori finite-energy condition on the limit. -/
theorem weightedFourier_tendsto_of_tendsto_eLpNorm_two
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hv : ∀ n, MemLp (v n) 2 volume) (hf : MemLp f 2 volume)
    (hvzero : ∀ n, ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0)
    (hlim : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0)) (ξ : ℝ) :
    Tendsto (fun n => weightedFourier (v n) ξ) atTop (𝓝 (weightedFourier f ξ)) :=
  ((tendstoUniformly_fourier_of_tendsto_eLpNorm_two hv hf hvzero hlim).tendsto_at ξ).const_smul _

/-- Identification of an unweighted Fourier L² limit from L¹ convergence
of the original integrable values, without any fixed-support hypothesis. -/
theorem fourier_ae_eq_of_tendsto_L1
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hv : ∀ n, Integrable (v n)) (hf : Integrable f)
    (hval : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 1 volume) atTop (𝓝 0))
    {F : ℕ → Lp ℂ 2 (volume : Measure ℝ)} {H : Lp ℂ 2 (volume : Measure ℝ)}
    (hFae : ∀ n, (F n : ℝ → ℂ) =ᵐ[volume] fourier (v n))
    (hFreq : Tendsto F atTop (𝓝 H)) :
    (H : ℝ → ℂ) =ᵐ[volume] fourier f := by
  obtain ⟨ns, hns, hnsconv⟩ := (tendstoInMeasure_of_tendsto_Lp hFreq).exists_seq_tendsto_ae
  filter_upwards [hnsconv, ae_all_iff.2 hFae] with ξ hξ hξae
  have hpoint := ((tendstoUniformly_fourier_of_tendsto_eLpNorm_one hv hf hval).tendsto_at ξ).comp
    hns.tendsto_atTop
  have hfreqpoint : Tendsto (fun n => (F (ns n) : ℝ → ℂ) ξ) atTop (𝓝 (fourier f ξ)) := by
    apply hpoint.congr'
    exact Eventually.of_forall fun n => (hξae (ns n)).symm
  exact tendsto_nhds_unique hξ hfreqpoint

/-- An L² limit of the actual unweighted Fourier integrals is identified
with the original integral of the value limit. -/
theorem fourier_ae_eq_of_tendsto
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hv : ∀ n, MemLp (v n) 2 volume) (hf : MemLp f 2 volume)
    (hvzero : ∀ n, ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0)
    (hval : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0))
    {F : ℕ → Lp ℂ 2 (volume : Measure ℝ)} {H : Lp ℂ 2 (volume : Measure ℝ)}
    (hFae : ∀ n, (F n : ℝ → ℂ) =ᵐ[volume] fourier (v n))
    (hFreq : Tendsto F atTop (𝓝 H)) :
    (H : ℝ → ℂ) =ᵐ[volume] fourier f := by
  obtain ⟨ns, hns, hnsconv⟩ := (tendstoInMeasure_of_tendsto_Lp hFreq).exists_seq_tendsto_ae
  filter_upwards [hnsconv, ae_all_iff.2 hFae] with ξ hξ hξae
  have hpoint := ((tendstoUniformly_fourier_of_tendsto_eLpNorm_two hv hf hvzero hval).tendsto_at ξ).comp
    hns.tendsto_atTop
  have hfreqpoint : Tendsto (fun n => (F (ns n) : ℝ → ℂ) ξ) atTop (𝓝 (fourier f ξ)) := by
    apply hpoint.congr'
    exact Eventually.of_forall fun n => (hξae (ns n)).symm
  exact tendsto_nhds_unique hξ hfreqpoint

/-- An L² frequency limit of the actual weighted Fourier integrals is the
weighted Fourier integral of the actual L² value limit. The identification
uses a.e. subsequential convergence and pointwise Fourier continuity. -/
theorem weightedFourier_ae_eq_of_tendsto
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hv : ∀ n, MemLp (v n) 2 volume) (hf : MemLp f 2 volume)
    (hvzero : ∀ n, ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0)
    (hval : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0))
    {F : ℕ → Lp ℂ 2 (volume : Measure ℝ)} {H : Lp ℂ 2 (volume : Measure ℝ)}
    (hFae : ∀ n, (F n : ℝ → ℂ) =ᵐ[volume] weightedFourier (v n))
    (hFreq : Tendsto F atTop (𝓝 H)) :
    (H : ℝ → ℂ) =ᵐ[volume] weightedFourier f := by
  obtain ⟨ns, hns, hnsconv⟩ := (tendstoInMeasure_of_tendsto_Lp hFreq).exists_seq_tendsto_ae
  filter_upwards [hnsconv, ae_all_iff.2 hFae] with ξ hξ hξae
  have hpoint := (weightedFourier_tendsto_of_tendsto_eLpNorm_two hv hf hvzero hval ξ).comp
    hns.tendsto_atTop
  have hfreqpoint : Tendsto (fun n => (F (ns n) : ℝ → ℂ) ξ) atTop
      (𝓝 (weightedFourier f ξ)) := by
    apply hpoint.congr'
    exact Eventually.of_forall fun n => (hξae (ns n)).symm
  exact tendsto_nhds_unique hξ hfreqpoint

/-- The actual restricted Fourier graph is closed under simultaneous L²
convergence of its value and weighted Fourier coordinates. In particular
finite energy of the limit is proved, rather than assumed. -/
theorem restricted_fourier_graph_limit
    {v : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hv : ∀ n, MemLp (v n) 2 volume) (hf : MemLp f 2 volume)
    (hvzero : ∀ n, ∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → v n x = 0)
    (hval : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0))
    {F : ℕ → Lp ℂ 2 (volume : Measure ℝ)} {H : Lp ℂ 2 (volume : Measure ℝ)}
    (hFae : ∀ n, (F n : ℝ → ℂ) =ᵐ[volume] weightedFourier (v n))
    (hFreq : Tendsto F atTop (𝓝 H)) :
    Integrable f ∧
      (∀ᵐ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x = 0) ∧
      FiniteEnergy f ∧ (H : ℝ → ℂ) =ᵐ[volume] weightedFourier f := by
  have hfzero := zero_exterior_of_tendsto_eLpNorm_two hv hf hvzero hval
  have hfi := integrable_of_memLp_two_zero_exterior hf hfzero
  have heq := weightedFourier_ae_eq_of_tendsto hv hf hvzero hval hFae hFreq
  have hfinite := (finiteEnergy_iff_memLp_weightedFourier hfi).mpr
    (MemLp.ae_eq heq (Lp.memLp H))
  exact ⟨hfi, hfzero, hfinite, heq⟩

end Torsion.Spectral

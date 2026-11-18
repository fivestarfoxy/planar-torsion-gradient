module

public import Torsion.Proof.PaperDeflectionMean
public import Torsion.Proof.PaperHolomorphicDiskVariance
public import Torsion.Proof.PaperDiskCenteredChart
public import Torsion.Proof.PaperDiskBoundaryAverage
public import Torsion.CanonicalSpectralCandidate

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The equal-area disk bounds the spectral frame's deflection -/

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology Pointwise
namespace Torsion.Spectral

/-- For the actual Cauchy conformal map, the pointwise torsion candidate is
at most the central displacement of the disk with the same area. -/
theorem physicalParameterExtension_le_disk {φ : ℝ → ℝ} (hφ : Continuous φ) (hodd : Function.Odd φ)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hpos : ∀ x ∈ Ioo (0:ℝ) 1, 0 < φ x)
    {w : Plane} (hw : w ∈ upperHalfPlane) :
    physicalParameterExtension φ w ≤ (volume (cauchyImage φ)).toReal / (4*Real.pi) := by
  let Z := centeredDiskChart w
  let F := cauchy φ ∘ Z
  let A := auxiliary φ ∘ Z
  let P := physicalParameterExtension φ ∘ Z
  let E := (volume (cauchyImage φ)).toReal
  have hm : MapsTo Z (ball 0 1) upperHalfPlane := centeredDiskChart_mapsTo hw
  have hZ : AnalyticOnNhd ℂ Z (ball 0 1) := centeredDiskChart_analyticOnNhd w
  have hF : AnalyticOnNhd ℂ F (ball 0 1) := (cauchy_analyticOnNhd hφ.continuousOn).comp hZ hm
  have hA : AnalyticOnNhd ℂ A (ball 0 1) := (auxiliary_analyticOnNhd hφ.continuousOn).comp hZ hm
  have hinj : InjOn F (ball 0 1) := (cauchy_injOn_upperHalfPlane hφ hodd hzero hpos).comp
    (centeredDiskChart_injOn hw) hm
  have hvol : volume (cauchyImage φ) ≠ ⊤ := (volume_cauchy_image_lt_top hφ hodd hzero).ne
  have hP (z : Plane) (hz : z ∈ ball 0 1) :
      P z = -(F z).im ^ 2 / 2 + (A z).im := physicalParameterExtension_eq_raw hφ.continuousOn (hm hz)
  have hav : Tendsto (fun r : ℝ => Real.circleAverage P 0 r) (𝓝[<] 1) (𝓝 0) := by
    apply diskChart_circleAverage_tendsto_zero hm hZ.continuousOn (centeredDiskChartInverse_mapsTo hw)
      (centeredDiskChartInverse_analyticOnNhd hw).continuousOn (fun _ hz => centeredDiskChartInverse_chart hw hz)
      (physicalParameterExtension_continuous hφ.continuousOn).continuousOn
    intro e he
    refine ⟨_, physicalParameterExtension_superlevel_isCompact hφ.continuousOn he,
      physicalParameterExtension_superlevel_subset he, ?_⟩
    exact fun z hz hval => ⟨subset_closure hz, by change e ≤ ‖physicalParameterExtension φ z‖; simpa only [Real.norm_eq_abs] using hval⟩
  have hevent : ∀ᶠ r : ℝ in 𝓝[<] 1, 2*Real.pi*P 0 ≤ (2*Real.pi)*Real.circleAverage P 0 r + E/2 := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))] with r hr hr0
    have hr1 : r < 1 := hr
    have hrs : closedBall (0:Plane) r ⊆ ball 0 1 := closedBall_subset_ball hr1
    have hbr : ball (0:Plane) r ⊆ ball 0 1 := ball_subset_ball hr1.le
    have H := conformal_deflection_mean hr0 (hF.mono hrs) (hA.mono hrs) (fun z hz => hP z (hrs hz))
    rw [angular_integral_eq_circleAverage] at H
    have Hvar := holomorphic_circle_variance_le_disk_energy isOpen_ball hF.differentiableOn hr0 hrs
    have Hen : (∫ z in ball (0:Plane) r, ‖deriv F z‖^2) ≤ E :=
      conformal_disk_energy_le_area (hF.mono hbr) (hinj.mono hbr)
        (fun z hz => ⟨Z z, hm (hbr hz), rfl⟩) hvol
    linarith
  have hlim : Tendsto (fun r : ℝ => (2*Real.pi)*Real.circleAverage P 0 r + E/2)
      (𝓝[<] 1) (𝓝 (E/2)) := by simpa using (hav.const_mul (2*Real.pi)).add_const (E/2)
  have heq : P 0 = physicalParameterExtension φ w := by simp [P,Z,centeredDiskChart_zero]
  have hh := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hevent
  rw [heq] at hh
  apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
  change _ ≤ E
  linarith

/-- The comparison holds at every physical point, including the exterior
where the genuine representative is zero. -/
theorem second_physical_deflection_le_disk (z : Plane) :
    physicalZeroExtension secondEigenfunction z ≤ secondCauchyDomain.area / (4*Real.pi) := by
  by_cases hz : z ∈ cauchyImage secondEigenfunction
  · rw [physicalZeroExtension_eq hz]
    obtain ⟨w,hw,rfl⟩ := hz
    rw [← physicalParameterExtension_eq_candidate secondEigenfunction_continuous secondEigenfunction_odd
      secondEigenfunction_zero_exterior secondEigenfunction_pos hw]
    exact physicalParameterExtension_le_disk secondEigenfunction_continuous secondEigenfunction_odd
      secondEigenfunction_zero_exterior secondEigenfunction_pos hw
  · rw [physicalZeroExtension_eq_zero hz]
    exact div_nonneg (by change 0 ≤ (volume _).toReal; positivity) (by positivity)

/-- On the actual area-one optimizer there is a genuine weak torsion pair
whose continuous displacement is bounded everywhere by the area-one disk's
central displacement. -/
theorem normalized_spectral_deflection_le_disk :
    ∃ (u : Plane → ℝ) (g : Plane → Plane),
      IsWeakTorsion (normalizedImage secondEigenvalue secondEigenfunction) u g ∧
        Continuous u ∧ ∀ z, u z ≤ 1/(4*Real.pi) := by
  let s := (Real.sqrt secondCauchyDomain.area)⁻¹
  have hE : 0 < secondCauchyDomain.area := secondCauchyDomain_area ▸ secondMoments.area_pos
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr hE)
  have hEq : normalizedImage secondEigenvalue secondEigenfunction = s • secondCauchyDomain.carrier := by
    rw [normalizedImage, ← secondCauchyDomain_area_spectral]
    rfl
  have hc := physicalZeroExtension_continuous secondEigenfunction_continuous secondEigenfunction_odd
    secondEigenfunction_zero_exterior secondEigenfunction_pos
  have hsc : Continuous (fun z : Plane => s⁻¹ • z) := continuous_const_smul _
  have hcont : Continuous (scaledValue s (physicalZeroExtension secondEigenfunction)) :=
    continuous_const.mul (hc.comp hsc)
  rw [hEq]
  refine ⟨_, _, secondCauchyDomain_isWeakTorsion.dilate s hs, hcont, ?_⟩
  intro z
  unfold scaledValue
  have hh := mul_le_mul_of_nonneg_left (second_physical_deflection_le_disk (s⁻¹ • z)) (sq_nonneg s)
  apply hh.trans_eq
  have hscale : s^2*secondCauchyDomain.area = 1 := by
    dsimp [s]
    rw [inv_pow, Real.sq_sqrt hE.le, inv_mul_cancel₀ hE.ne']
  rw [← mul_div_assoc, hscale]

end Torsion.Spectral

module

public import Torsion.Proof.PaperMaximizerApproximation
public import Torsion.Proof.PaperFrameLimit
public import Torsion.CanonicalOptimization

@[expose] public section

/-! # Rigidity in the coordinates of a maximizing normal quotient -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Torsion.Spectral

/-- In coordinates based at any maximizing normal quotient, an area-one
extremizer equals the canonical domain in those very coordinates. This
identifies the marked point as the middle of its flat side. -/
theorem second_area_one_rigidity_at_maximizing_quotient (D : ConvexDomain)
    (hA : D.area = 1) {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D.carrier u g)
    (hc : ContinuousOn u D.carrier) (hzero : (0 : Plane) ∈ closure D.carrier)
    (hhalf : D.carrier ⊆ upperHalfPlane)
    (hline : ∀ᶠ t : ℝ in 𝓝[>] 0, (t : Plane) * Complex.I ∈ D.carrier)
    (hq : HasMarkedFlux u (spectralConstant secondEigenvalue secondEigenfunction)) :
    D.carrier = normalizedImage secondEigenvalue secondEigenfunction := by
  let δ (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hd (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  let R (n : ℕ) := supportingRadialProfile D hzero (δ n) (hd n)
  have hR (n : ℕ) := supportingRadialProfile_pos D hzero (hd n)
  have hsub (n : ℕ) := subset_radialDomain_supportingRadialProfile D hzero hhalf (hd n)
  have ha := radialArea_supportingRadialProfile_tendsto D hzero hhalf δ hd
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [hA] at ha
  have hq' (n : ℕ) := hq.le_of_weakTorsion_subset_marked hu hc D.isOpen D.bounded hhalf
    (ContinuousProfiles.domain_isMarked (hR n)) (hsub n)
    (torsionFlux_spec (ContinuousProfiles.domain_isMarked (hR n))) hline
  have hlim := radial_observation_excess_tendsto R hR (fun _ => 0) tendsto_const_nhds ha
    (fun n => by simpa only [sub_zero, mul_one] using hq' n)
  obtain ⟨K, hK, hKA, _⟩ := second_exact_value.2
  rw [← hK] at hlim ⊢
  apply D.carrier_eq_of_area_eq_of_volume_sdiff_eq_zero K (hA.trans hKA.symm)
  apply le_antisymm _ bot_le
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  exact Eventually.of_forall (fun k => measure_mono (sdiff_subset_sdiff_left (hsub k)))

end Torsion.Spectral

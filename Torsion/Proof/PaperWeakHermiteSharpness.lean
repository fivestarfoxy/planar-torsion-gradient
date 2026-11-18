module

public import Torsion.Proof.PaperHarmonicData
public import Torsion.Proof.PaperHarmonicApproximation

@[expose] public section

/-! # Sharpness for the actual weak torsion and physical boundary measure

A coefficient valid on compact smooth subharmonic tests also bounds the volume
of the harmonic extension of every smooth nonnegative boundary datum. Applying
this to concentrating data compares the limits of the weak torsion flux and
the true arclength, without any differentiability hypothesis on torsion at the
boundary. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Torsion.HermiteHadamard
open WeakHarmonicRegularity

/-- A candidate Hermite–Hadamard coefficient, tested on actual compact smooth
functions with nonnegative boundary data and nonnegative interior Laplacian. -/
def BoundsSmoothTests (D : ConvexDomain) (σ : Measure Plane) (C : ℝ) : Prop :=
  ∀ f : Plane → ℝ, IsTest univ f → (∀ z ∈ D.carrier, 0 ≤ planarLaplacian f z) →
    (∀ z ∈ frontier D.carrier, 0 ≤ f z) → (∫ z in D.carrier, f z) ≤ C * ∫ z, f z ∂σ

/-- Testing the coefficient only on smooth compact functions harmonic in the
domain requires a smaller class of test functions. -/
def BoundsHarmonicTests (D : ConvexDomain) (σ : Measure Plane) (C : ℝ) : Prop :=
  ∀ f : Plane → ℝ, IsTest univ f → (∀ z ∈ D.carrier, planarLaplacian f z = 0) →
    (∀ z ∈ frontier D.carrier, 0 ≤ f z) → (∫ z in D.carrier, f z) ≤ C * ∫ z, f z ∂σ

theorem BoundsSmoothTests.toHarmonic {D : ConvexDomain} {σ : Measure Plane} {C : ℝ}
    (h : BoundsSmoothTests D σ C) : BoundsHarmonicTests D σ C :=
  fun f hf hh => h f hf (fun z hz => (hh z hz).ge)

/-- Every admissible smooth-test coefficient bounds the original weak torsion
flux against every smooth nonnegative boundary datum. -/
theorem BoundsHarmonicTests.weak_flux_le {D : ConvexDomain} {σ : Measure Plane} [IsFiniteMeasure σ]
    {C : ℝ} (hC : BoundsHarmonicTests D σ C) (hsupp : ∀ᵐ z ∂σ, z ∈ frontier D.carrier)
    {u b : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D.carrier u g)
    (hb : IsTest univ b) (hb0 : ∀ z, 0 ≤ b z) :
    (∫ z in D.carrier, b z) - (∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (gradient b z))
      ≤ C * ∫ z, b z ∂σ := by
  obtain ⟨H, hc, hs, hh, hz, hgreen⟩ := exists_continuous_harmonic_extension_with_integral D hb
  rw [← hgreen hu]
  by_contra! hfalse
  let m := σ.real univ
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  let A := (∫ z in D.carrier, H z) - C * ∫ z, b z ∂σ
  have hA : 0 < A := sub_pos.mpr hfalse
  let E := |C| * m + 1
  have hE : 0 < E := by dsimp only [E]; positivity
  let δ := A / E
  have hδ : 0 < δ := div_pos hA hE
  obtain ⟨f, W, hf, _, hW, hWf, hnear⟩ :=
    exists_compact_harmonic_upper_approximation D hc hs hh hδ
  have htrace (z : Plane) (hsurf : z ∈ frontier D.carrier) :
      b z < f z ∧ f z < b z + δ := by
    have h := hnear z (frontier_subset_closure hsurf)
    rwa [hz z (D.isOpen.frontier_eq ▸ hsurf).2] at h
  have hfI := hf.1.continuous.integrable_of_hasCompactSupport (μ := σ) hf.2.1
  have hbI := hb.1.continuous.integrable_of_hasCompactSupport (μ := σ) hb.2.1
  have hvol : (∫ z in D.carrier, H z) ≤ ∫ z in D.carrier, f z := by
    apply setIntegral_mono_on
      ((hc.continuousOn.integrableOn_compact D.bounded.isCompact_closure).mono_set subset_closure)
      ((hf.1.continuous.continuousOn.integrableOn_compact D.bounded.isCompact_closure).mono_set subset_closure)
      D.isOpen.measurableSet
    intro z h
    exact (hnear z (subset_closure h)).1.le
  have hab := hC f hf (fun z h => hWf z (hW (subset_closure h)))
    (fun z h => (hb0 z).trans (htrace z h).1.le)
  have hl : (∫ z, b z ∂σ) ≤ ∫ z, f z ∂σ := integral_mono_ae hbI hfI
    (hsupp.mono fun z h => (htrace z h).1.le)
  have hupp : (∫ z, f z ∂σ) ≤ (∫ z, b z ∂σ) + m * δ := by
    calc
      _ ≤ ∫ z, b z + δ ∂σ := integral_mono_ae hfI (hbI.add (integrable_const _))
        (hsupp.mono fun z h => (htrace z h).2.le)
      _ = _ := by rw [integral_add hbI (integrable_const _), integral_const]; rfl
  have hscale : A ≤ |C| * m * δ := by
    rcases le_total 0 C with hpos | hneg
    · have h := mul_le_mul_of_nonneg_left hupp hpos
      dsimp only [A]
      rw [abs_of_nonneg hpos]
      nlinarith
    · have h := mul_le_mul_of_nonpos_left hl hneg
      have hnon : 0 ≤ |C| * m * δ := by positivity
      dsimp only [A]
      linarith
  have heq : δ * E = A := div_mul_cancel₀ _ hE.ne'
  dsimp only [E] at heq
  nlinarith

/-- Recovery of the sharp coefficient from scaled weak torsion flux and
physical boundary mass. Both limits may be taken over a continuous positive
scale tending to zero. -/
theorem BoundsHarmonicTests.coefficient_ge_of_flux_limits {D : ConvexDomain}
    {σ : Measure Plane} [IsFiniteMeasure σ] {C : ℝ} (hC : BoundsHarmonicTests D σ C)
    (hsupp : ∀ᵐ z ∂σ, z ∈ frontier D.carrier) {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D.carrier u g) (b : ℝ → Plane → ℝ)
    (hb : ∀ r > 0, IsTest univ (b r)) (hb0 : ∀ r > 0, ∀ z, 0 ≤ b r z)
    {G I : ℝ} (hI : 0 < I)
    (hflux : Tendsto (fun r : ℝ => r⁻¹ * ((∫ z in D.carrier, b r z) -
      ∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (gradient (b r) z))) (𝓝[>] 0) (𝓝 (G * I)))
    (hmass : Tendsto (fun r : ℝ => r⁻¹ * ∫ z, b r z ∂σ) (𝓝[>] 0) (𝓝 I)) :
    G ≤ C := by
  have hle : (fun r : ℝ => r⁻¹ * ((∫ z in D.carrier, b r z) -
      ∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (gradient (b r) z))) ≤ᶠ[𝓝[>] 0]
      (fun r : ℝ => C * (r⁻¹ * ∫ z, b r z ∂σ)) := by
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with r hr
    have h := mul_le_mul_of_nonneg_left (hC.weak_flux_le hsupp hu (hb r hr) (hb0 r hr))
      (inv_nonneg.mpr hr.le)
    exact h.trans_eq (by ring)
  exact (mul_le_mul_iff_of_pos_right hI).mp (le_of_tendsto_of_tendsto hflux (hmass.const_mul C) hle)

/-- Every admissible smooth-test coefficient bounds the original weak torsion
flux against every smooth nonnegative boundary datum. -/
theorem BoundsSmoothTests.weak_flux_le {D : ConvexDomain} {σ : Measure Plane} [IsFiniteMeasure σ]
    {C : ℝ} (hC : BoundsSmoothTests D σ C) (hsupp : ∀ᵐ z ∂σ, z ∈ frontier D.carrier)
    {u b : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D.carrier u g)
    (hb : IsTest univ b) (hb0 : ∀ z, 0 ≤ b z) :
    (∫ z in D.carrier, b z) - (∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (gradient b z))
      ≤ C * ∫ z, b z ∂σ :=
  hC.toHarmonic.weak_flux_le hsupp hu hb hb0

/-- Recovery of the sharp coefficient from scaled weak torsion flux and
physical boundary mass. Both limits may be taken over a continuous positive
scale tending to zero. -/
theorem BoundsSmoothTests.coefficient_ge_of_flux_limits {D : ConvexDomain}
    {σ : Measure Plane} [IsFiniteMeasure σ] {C : ℝ} (hC : BoundsSmoothTests D σ C)
    (hsupp : ∀ᵐ z ∂σ, z ∈ frontier D.carrier) {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D.carrier u g) (b : ℝ → Plane → ℝ)
    (hb : ∀ r > 0, IsTest univ (b r)) (hb0 : ∀ r > 0, ∀ z, 0 ≤ b r z)
    {G I : ℝ} (hI : 0 < I)
    (hflux : Tendsto (fun r : ℝ => r⁻¹ * ((∫ z in D.carrier, b r z) -
      ∫ z in D.carrier, inner (𝕜 := ℝ) (g z) (gradient (b r) z))) (𝓝[>] 0) (𝓝 (G * I)))
    (hmass : Tendsto (fun r : ℝ => r⁻¹ * ∫ z, b r z ∂σ) (𝓝[>] 0) (𝓝 I)) :
    G ≤ C :=
  hC.toHarmonic.coefficient_ge_of_flux_limits hsupp hu b hb hb0 hI hflux hmass

end Torsion.HermiteHadamard

import Torsion.CauchyTracePairingLimit
import Torsion.FourierHilbertPairing
import Torsion.PhysicalCauchyMarkedFlux

/-!
# The linear Hilbert equation from the actual restricted eigenfunction

The exponentially damped Fourier multiplier is the actual conjugate Poisson
kernel. Removing damping and passing to the genuine continuous Cauchy trace
identifies the concrete Fourier form with its trace pairing. Distributional
test separation then derives the pointwise linear Hilbert equation from the
original weak eigenfunction equation; that equation is no longer an input.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff
namespace Torsion.Spectral

/-- The actual half-Laplacian energy of the integrated profile is the
pairing against its actual continuous real Cauchy trace. -/
theorem energy_height_eq_realCauchyBoundary_pairing
    {φ ψ : ℝ → ℝ} {C α : ℝ≥0}
    (hφ : HolderWith C α φ) (hα : 0 < α) (hodd : Function.Odd φ)
    (hzero : ∀ s : ℝ, 1 ≤ |s| → φ s = 0) (hE : FiniteEnergy φ)
    (hψ : IsCore ψ) :
    energy (height φ) ψ = ∫ x : ℝ, ψ x * realCauchyBoundaryRe φ x := by
  have hc := hφ.continuous hα
  have hlimE := damped_energy_tendsto (height_integrable hc.continuousOn)
    (hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1)
    (finiteEnergy_height hc hodd hzero hE)
    (finiteEnergy_of_contDiff_hasCompactSupport hψ.1 hψ.2.1)
  have hlimT := realCauchy_pairing_tendsto_boundary hφ hα hzero hψ
  have heq : (fun y : ℝ => (1 / (2 * Real.pi)) * ∫ ξ : ℝ,
      Real.exp (-y * |ξ|) * |ξ| *
        (fourier (height φ) ξ * star (fourier ψ ξ)).re) =ᶠ[𝓝[>] 0]
      (fun y : ℝ => ∫ x : ℝ,
        ψ x * (realCauchy φ ((x : ℂ) + (y : ℂ) * Complex.I)).re) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa only [mul_assoc] using
      damped_energy_height_eq_realCauchy_pairing hc hodd hzero
        (hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1) hy
  exact tendsto_nhds_unique hlimE (hlimT.congr' heq.symm)

/-- The original Fourier-form weak eigenfunction equation implies the
actual pointwise linear Hilbert equation on the interval, with a unique
constant. Only the stated oddness and Hölder regularity remain as spectral
inputs; no linear Hilbert equation or multiplier identity is assumed. -/
theorem IsRestrictedEigenfunction.linear_hilbert_equation
    {a : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ)
    (hφ : HolderWith C α φ) (hα : 0 < α) (hodd : Function.Odd φ) :
    ∃! b : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b := by
  have hpair : ∀ ψ : ℝ → ℝ, IsCore ψ → energy (height φ) ψ =
      ∫ x : ℝ, ψ x * realCauchyBoundaryRe φ x := by
    intro ψ hψ
    exact energy_height_eq_realCauchyBoundary_pairing hφ hα hodd
      (hEig.1.zero_exterior (hφ.continuous hα)) hEig.1.2.1 hψ
  have hc := hφ.continuous hα
  have hzero := hEig.1.zero_exterior hc
  have ht := realCauchyBoundaryRe_continuous hφ hα hzero
  have hY := height_continuous hc.continuousOn
  obtain ⟨b, hb⟩ := hEig.height_equation hc hodd
  let F : ℝ → ℝ := fun x => realCauchyBoundaryRe φ x - (a * height φ x - b)
  have hFc : Continuous F := ht.sub (continuous_const.mul hY |>.sub continuous_const)
  have hFae : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → F x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hFc.locallyIntegrable.locallyIntegrableOn _)
    intro ψ hψ hcomp hsupp
    have hcore : IsCore ψ := ⟨hψ, hcomp, hsupp⟩
    have heq := hb ψ hcore
    rw [hpair ψ hcore] at heq
    have hi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hcomp
    have hiT : Integrable (fun x => ψ x * realCauchyBoundaryRe φ x) :=
      (hψ.continuous.mul ht).integrable_of_hasCompactSupport hcomp.mul_right
    have hiY : Integrable (fun x => height φ x * ψ x) :=
      (hY.mul hψ.continuous).integrable_of_hasCompactSupport hcomp.mul_left
    calc
      (∫ x : ℝ, ψ x • F x) = ∫ x : ℝ,
          ψ x * realCauchyBoundaryRe φ x - a * (height φ x * ψ x) + b * ψ x := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by dsimp only [F]; simp only [smul_eq_mul]; ring
      _ = 0 := by
        rw [integral_add (f := fun x => ψ x * realCauchyBoundaryRe φ x -
          a * (height φ x * ψ x)) (g := fun x => b * ψ x)
          (hiT.sub (hiY.const_mul a)) (hi.const_mul b),
          integral_sub (f := fun x => ψ x * realCauchyBoundaryRe φ x)
            (g := fun x => a * (height φ x * ψ x)) hiT (hiY.const_mul a),
          integral_const_mul, integral_const_mul]
        linarith
  have hFeq : EqOn F (fun _ => 0) (Ioo (-1 : ℝ) 1) := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume)
      ((ae_restrict_iff' measurableSet_Ioo).mpr hFae) isOpen_Ioo
      hFc.continuousOn continuousOn_const
  have hpoint : ∀ x ∈ Ioo (-1 : ℝ) 1,
      realCauchyBoundaryRe φ x = a * height φ x - b := by
    intro x hx
    exact sub_eq_zero.mp (hFeq hx)
  refine ⟨b, hpoint, ?_⟩
  intro c hc'
  have h₁ := hpoint 0 (by norm_num)
  have h₂ := hc' 0 (by norm_num)
  linarith

/-- The actual weak eigenfunction now supplies the linear equation used by
the exact Cauchy torsion construction. The weak PDE and marked flux are
conclusions, rather than additional spectral hypotheses. -/
theorem IsRestrictedEigenfunction.cauchy_torsion_construction
    {a : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x) :
    ∃ b : ℝ, 0 < b ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, realCauchyBoundaryRe φ x = a * height φ x - b) ∧
      a * squareMass φ = 2 * b * mass φ ∧
      IsWeakTorsion (cauchyImage φ) (physicalZeroExtension φ) (physicalZeroGradient φ) ∧
      torsionFlux (cauchyImage φ) = b / a := by
  obtain ⟨b, hb, _⟩ := hEig.linear_hilbert_equation hφ hα0 hodd
  have ha := hEig.eigenvalue_pos
  have hzero := hEig.1.zero_exterior (hφ.continuous hα0)
  exact ⟨b,
    (coefficient_pos_and_unique_velocity_zero_of_holder_boundary_equation
      ha hφ hα0 hα1 hodd hzero hpos hb).1,
    hb,
    moment_identity_of_holder_boundary_equation ha.ne' hφ hα0 hα1 hodd hzero hb,
    physicalCandidate_isWeakTorsion ha.ne' hφ hα0 hα1 hodd hzero hpos hb,
    torsionFlux_cauchyImage ha.ne' hφ hα0 hα1 hodd hzero hpos hb⟩

end Torsion.Spectral

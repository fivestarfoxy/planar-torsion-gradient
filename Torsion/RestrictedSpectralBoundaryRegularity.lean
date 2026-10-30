import Torsion.RestrictedSpectralBoundaryPrimitive
import Torsion.RestrictedSpectralWeakIntegrated

/-!
# Interior differentiability of the actual height's Cauchy boundary value

The weak equation and the automatically proved one-half Hölder estimate
for the height give a classical derivative of its genuine real Cauchy
boundary value. No continuity or Hölder regularity of the eigenfunction is
assumed here.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace Torsion.Spectral

/-- A continuous function whose weak derivative vanishes on the original
interval is constant there, proved using the actual compact smooth tests. -/
theorem eqOn_const_of_continuous_of_core_derivative_pairing_zero
    {D : ℝ → ℝ} (hD : Continuous D)
    (hweak : ∀ ψ : ℝ → ℝ, IsCore ψ → (∫ x : ℝ, D x * deriv ψ x) = 0) :
    ∃ c : ℝ, EqOn D (fun _ => c) (Ioo (-1 : ℝ) 1) := by
  obtain ⟨ρ, hρ, hρmean⟩ := exists_core_integral_one
  let c : ℝ := ∫ x : ℝ, D x * ρ x
  have hpair (ψ : ℝ → ℝ) (hψ : IsCore ψ) :
      (∫ x : ℝ, D x * ψ x) = c * ∫ x : ℝ, ψ x := by
    let m : ℝ := ∫ x : ℝ, ψ x
    let χ : ℝ → ℝ := fun x => ψ x + (-m) * ρ x
    have hχ : IsCore χ := by
      simpa only [one_mul] using hψ.linear_combination hρ 1 (-m)
    have hiψ : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
    have hiρ : Integrable ρ := hρ.1.continuous.integrable_of_hasCompactSupport hρ.2.1
    have hmean : (∫ x : ℝ, χ x) = 0 := by
      dsimp only [χ]
      rw [integral_add hiψ (hiρ.const_mul (-m)), integral_const_mul, hρmean]
      dsimp only [m]
      ring
    obtain ⟨P, hP, hdP⟩ := hχ.exists_primitive_of_integral_eq_zero hmean
    have h := hweak P hP
    rw [hdP] at h
    have hiDψ : Integrable (fun x => D x * ψ x) :=
      (hD.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
    have hiDρ : Integrable (fun x => D x * ρ x) :=
      (hD.mul hρ.1.continuous).integrable_of_hasCompactSupport hρ.2.1.mul_left
    have hI : (∫ x : ℝ, D x * χ x) =
        (∫ x : ℝ, D x * ψ x) + (-m) * ∫ x : ℝ, D x * ρ x := by
      calc
        _ = ∫ x : ℝ, D x * ψ x + (-m) * (D x * ρ x) := by
          congr 1
          funext x
          dsimp only [χ]
          ring
        _ = _ := by rw [integral_add hiDψ (hiDρ.const_mul (-m)), integral_const_mul]
    rw [hI] at h
    change (∫ x : ℝ, D x * ψ x) = c * m
    dsimp only [c] at *
    linarith
  have hae : ∀ᵐ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → D x - c = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hD.sub continuous_const).locallyIntegrable.locallyIntegrableOn _)
    intro ψ hψ hcomp hsupp
    have hcore : IsCore ψ := ⟨hψ, hcomp, hsupp⟩
    have h := hpair ψ hcore
    have hi1 : Integrable (fun x => D x * ψ x) :=
      (hD.mul hψ.continuous).integrable_of_hasCompactSupport hcomp.mul_left
    have hi2 : Integrable (fun x => c * ψ x) :=
      (hψ.continuous.integrable_of_hasCompactSupport hcomp).const_mul c
    calc
      (∫ x : ℝ, ψ x • (D x - c)) = ∫ x : ℝ, D x * ψ x - c * ψ x := by
        congr 1
        funext x
        simp only [smul_eq_mul]
        ring
      _ = 0 := by rw [integral_sub hi1 hi2, integral_const_mul, h, sub_self]
  have heq : EqOn (fun x => D x - c) (fun _ => 0) (Ioo (-1 : ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq (μ := volume)
      ((ae_restrict_iff' measurableSet_Ioo).mpr hae) isOpen_Ioo
      (hD.sub continuous_const).continuousOn continuousOn_const
  exact ⟨c, fun x hx => sub_eq_zero.mp (heq hx)⟩

/-- A classical interior derivative of the actual continuous Cauchy
boundary value of the height follows from the original weak eigenfunction
equation and oddness alone. -/
theorem IsRestrictedEigenfunction.height_Cauchy_boundary_hasDerivAt
    {a : ℝ} {φ : ℝ → ℝ} (hEig : IsRestrictedEigenfunction a φ)
    (hodd : Function.Odd φ) :
    ∃ b : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (realCauchyBoundaryRe (height φ)) (-a * height φ x + b) x := by
  obtain ⟨C, hYH⟩ := hEig.1.height_holder_half
  have hα : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hYc := hEig.1.height_continuous
  have hYzero : ∀ x : ℝ, 1 ≤ |x| → height φ x = 0 :=
    fun x hx => height_zero_of_one_le_abs φ hx
  have hR : Continuous (realCauchyBoundaryRe (height φ)) :=
    realCauchyBoundaryRe_continuous hYH hα hYzero
  obtain ⟨b, hb⟩ := hEig.height_equation_of_odd hodd
  let g : ℝ → ℝ := fun x => -a * height φ x + b
  have hgc : Continuous g := (continuous_const.mul hYc).add continuous_const
  let P : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t
  have hdP (x : ℝ) : HasDerivAt P (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable 0 x)
      hgc.stronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun x => (hdP x).continuousAt
  have hweak (ψ : ℝ → ℝ) (hψ : IsCore ψ) :
      (∫ x : ℝ, (realCauchyBoundaryRe (height φ) x - P x) * deriv ψ x) = 0 := by
    have hRpair := energy_eq_realCauchyBoundary_deriv_pairing hYH hα hYzero
      (hEig.1.finiteEnergy_height hodd) hψ
    have hPpair := integral_mul_deriv_eq_deriv_mul_of_integrable hdP
      (fun x => (hψ.1.differentiable (by simp) x).hasDerivAt)
      ((hPc.mul hψ.deriv.1.continuous).integrable_of_hasCompactSupport hψ.deriv.2.1.mul_left)
      ((hgc.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left)
      ((hPc.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left)
    have hiYψ : Integrable (fun x => height φ x * ψ x) :=
      (hYc.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
    have hiψ : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
    have hgpair : (∫ x : ℝ, g x * ψ x) =
        -a * (∫ x : ℝ, height φ x * ψ x) + b * ∫ x : ℝ, ψ x := by
      calc
        _ = ∫ x : ℝ, -a * (height φ x * ψ x) + b * ψ x := by
          congr 1
          funext x
          dsimp only [g]
          ring
        _ = _ := by rw [integral_add (hiYψ.const_mul (-a)) (hiψ.const_mul b),
          integral_const_mul, integral_const_mul]
    rw [hgpair] at hPpair
    have hiR : Integrable (fun x => realCauchyBoundaryRe (height φ) x * deriv ψ x) :=
      (hR.mul hψ.deriv.1.continuous).integrable_of_hasCompactSupport hψ.deriv.2.1.mul_left
    have hiP : Integrable (fun x => P x * deriv ψ x) :=
      (hPc.mul hψ.deriv.1.continuous).integrable_of_hasCompactSupport hψ.deriv.2.1.mul_left
    calc
      _ = (∫ x : ℝ, realCauchyBoundaryRe (height φ) x * deriv ψ x) -
          ∫ x : ℝ, P x * deriv ψ x := by
        rw [← integral_sub hiR hiP]
        congr 1
        funext x
        ring
      _ = 0 := by
        have hRpair' : (∫ x : ℝ, realCauchyBoundaryRe (height φ) x * deriv ψ x) =
            energy (height φ) ψ := by
          rw [hRpair]
          congr 1
          funext x
          ring
        rw [hRpair', hb ψ hψ]
        simpa only [Pi.mul_apply] using (by linarith [hPpair] :
          a * (∫ x : ℝ, height φ x * ψ x) - b * (∫ x : ℝ, ψ x) -
            (∫ x : ℝ, P x * deriv ψ x) = 0)
  obtain ⟨c, hc⟩ := eqOn_const_of_continuous_of_core_derivative_pairing_zero
    (hR.sub hPc) hweak
  refine ⟨b, fun x hx => ?_⟩
  have heq : realCauchyBoundaryRe (height φ) =ᶠ[𝓝 x] fun t => P t + c := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    have h := hc ht
    change realCauchyBoundaryRe (height φ) t - P t = c at h
    linarith
  exact ((hdP x).add_const c).congr_of_eventuallyEq heq

end Torsion.Spectral

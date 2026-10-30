import Torsion.RestrictedSpectralResolvent
import Torsion.RestrictedSpectralSymmetry

/-!
# Actual reflection symmetry of the restricted resolvent

Reflection is the actual measure-preserving composition operator on real
L². The concrete Fourier-form reflection identity and actual weak
uniqueness show that the constructed Lax--Milgram resolvent commutes with
this involutive isometry.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- Uniqueness in the actual restricted form domain, tested with the
actual difference. This is uniqueness for the original Fourier form. -/
theorem restricted_weak_unique {u v : Lp ℝ 2 (volume : Measure ℝ)}
    (hu : MemRestrictedFormDomain (u : ℝ → ℝ))
    (hv : MemRestrictedFormDomain (v : ℝ → ℝ))
    (heq : ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
      energy (u : ℝ → ℝ) ψ = energy (v : ℝ → ℝ) ψ) : u = v := by
  let d : ℝ → ℝ := fun x => u x - v x
  have hd : MemRestrictedFormDomain d := by
    simpa only [d, sub_eq_add_neg, neg_one_mul] using hu.add (hv.const_mul (-1))
  have hE : energy d d = 0 := by
    have heqd : d = fun x => u x + (-1 : ℝ) * v x := by funext x; dsimp only [d]; ring
    calc
      energy d d = energy (fun x => u x + (-1 : ℝ) * v x) d :=
        congrArg (fun k : ℝ → ℝ => energy k d) heqd
      _ = energy (u : ℝ → ℝ) d - energy (v : ℝ → ℝ) d := by
        rw [energy_add_left hu.integrable (hv.integrable.const_mul (-1))
          hd.integrable hu.2.1 (FiniteEnergy.const_mul hv.integrable hv.2.1 (-1)) hd.2.1,
          energy_const_mul_left]
        ring
      _ = 0 := sub_eq_zero.mpr (heq d hd)
  have hd0 := (energy_eq_zero_iff hd.integrable hd.2.1).mp hE
  apply Lp.ext
  filter_upwards [hd0] with x hx
  change u x - v x = 0 at hx
  exact sub_eq_zero.mp hx

namespace RestrictedHilbert

/-- The actual bounded real-L² reflection `u(x) ↦ u(-x)`. -/
def reflection : ValueL2 →L[ℝ] ValueL2 :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x : ℝ => -x)
    (Measure.measurePreserving_neg (volume : Measure ℝ))).toContinuousLinearMap

/-- Reflection acts on actual representatives by composition with negation. -/
theorem reflection_ae (u : ValueL2) :
    (reflection u : ℝ → ℝ) =ᵐ[volume] fun x => u (-x) :=
  Lp.coeFn_compMeasurePreserving u (Measure.measurePreserving_neg volume)

@[simp] theorem reflection_norm (u : ValueL2) : ‖reflection u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u (Measure.measurePreserving_neg volume)

theorem reflection_isometry : Isometry reflection :=
  Lp.isometry_compMeasurePreserving (Measure.measurePreserving_neg volume)

@[simp] theorem reflection_involutive (u : ValueL2) : reflection (reflection u) = u := by
  apply Lp.ext
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (reflection_ae u)
  filter_upwards [reflection_ae (reflection u), h] with x hx hy
  simpa only [neg_neg] using hx.trans hy

/-- Exact behavior of the reflection operator on an original L² function. -/
theorem reflection_toLp {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    reflection (hf.toLp f) =
      (hf.comp_measurePreserving (Measure.measurePreserving_neg volume)).toLp (fun x => f (-x)) := rfl

/-- Pointwise odd original functions give actual odd L² vectors. -/
theorem reflection_of_odd {f : ℝ → ℝ} (hf : MemLp f 2 volume) (hodd : Function.Odd f) :
    reflection (hf.toLp f) = -hf.toLp f := by
  apply Lp.ext
  have hfneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hf.coeFn_toLp
  filter_upwards [reflection_ae (hf.toLp f), hfneg, hf.coeFn_toLp,
    Lp.coeFn_neg (hf.toLp f)] with x hx hneg hval hminus
  simp only [Pi.neg_apply] at hminus
  rw [hx, hneg, hminus, hval, hodd x]

/-- Reflection is symmetric for the actual real L² pairing. -/
theorem reflection_inner_left (u v : ValueL2) :
    inner (𝕜 := ℝ) (reflection u) v = inner (𝕜 := ℝ) u (reflection v) := by
  calc
    _ = ∫ x : ℝ, u (-x) * v x := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [reflection_ae u] with x hx
      change v x * (reflection u) x = u (-x) * v x
      rw [hx]
      ring
    _ = ∫ x : ℝ, u x * v (-x) := by
      simpa only [neg_neg] using integral_neg_eq_self (fun x : ℝ => u x * v (-x)) volume
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [reflection_ae v] with x hx
      change u x * v (-x) = (reflection v) x * u x
      rw [hx]
      ring

theorem reflection_isSelfAdjoint : IsSelfAdjoint reflection := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro u v
  exact reflection_inner_left u v

/-- Reflection transports the actual weak resolvent equation, using the
actual source and test functions and the proved Fourier reflection law. -/
theorem reflected_resolvent_equation (f : ValueL2) {ψ : ℝ → ℝ}
    (hψ : MemRestrictedFormDomain ψ) :
    Torsion.Spectral.energy (fun x => (resolvent f) (-x)) ψ =
      ∫ x : ℝ, (reflection f) x * ψ x := by
  rw [energy_reflect_left, solutionOperator_equation f hψ.reflect]
  calc
    (∫ x : ℝ, f x * ψ (-x)) = ∫ x : ℝ, f (-x) * ψ x := by
      simpa only [neg_neg] using
        (integral_neg_eq_self (fun x : ℝ => f x * ψ (-x)) volume).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [reflection_ae f] with x hx
      rw [hx]

/-- The constructed actual restricted resolvent commutes with reflection.
This follows from actual Fourier-form invariance and weak uniqueness. -/
theorem resolvent_reflection (f : ValueL2) :
    resolvent (reflection f) = reflection (resolvent f) := by
  have hu : MemRestrictedFormDomain (resolvent (reflection f) : ℝ → ℝ) :=
    memRestrictedFormDomain_coordinates (solutionOperator (reflection f))
  have hv : MemRestrictedFormDomain (reflection (resolvent f) : ℝ → ℝ) :=
    (memRestrictedFormDomain_coordinates (solutionOperator f)).reflect.congr_ae
      (reflection_ae (resolvent f)).symm
  apply restricted_weak_unique hu hv
  intro ψ hψ
  calc
    _ = ∫ x : ℝ, (reflection f) x * ψ x := solutionOperator_equation (reflection f) hψ
    _ = Torsion.Spectral.energy (fun x => (resolvent f) (-x)) ψ :=
      (reflected_resolvent_equation f hψ).symm
    _ = _ := (energy_congr_ae (reflection_ae (resolvent f)) (Filter.EventuallyEq.rfl)).symm

end RestrictedHilbert
end Torsion.Spectral

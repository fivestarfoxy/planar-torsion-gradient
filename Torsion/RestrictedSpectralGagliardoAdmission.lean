import Torsion.SobolevBoundaryAdmission
import Torsion.RestrictedSpectralWeakClosure
import Torsion.RestrictedSpectralGagliardo

/-!
# Admission of continuous positive interior data from its actual difference energy

Flat positive-level truncations give genuine compact smooth tests. Their
pointwise scalar contraction bounds the original Fourier energies by the
actual finite Gagliardo integral, and weak graph closure then proves membership
in the existing restricted form domain.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- Positive level truncation in the value variable gives actual restricted
smooth core functions whenever the zero extension is continuous and smooth
inside the interval. -/
theorem positiveLevelTruncation_isCore {f : ℝ → ℝ}
    (hc : Continuous f) (hs : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hz : ∀ x ∉ Ioo (-1 : ℝ) 1, f x = 0) (n : ℕ) :
    IsCore (fun x => BoundaryAdmission.truncation n (f x)) := by
  have hlevel : IsClosed {x : ℝ | BoundaryAdmission.threshold n ≤ f x} :=
    isClosed_le continuous_const hc
  have hsupport : Function.support (fun x => BoundaryAdmission.truncation n (f x)) ⊆
      {x : ℝ | BoundaryAdmission.threshold n ≤ f x} := by
    intro x hx
    by_contra h
    exact hx (BoundaryAdmission.truncation_zero_of_le n (le_of_not_ge h))
  have htsupport := closure_minimal hsupport hlevel
  have hsub : tsupport (fun x => BoundaryAdmission.truncation n (f x)) ⊆
      Ioo (-1 : ℝ) 1 := by
    intro x hx
    by_contra hxD
    have hx' := htsupport hx
    change BoundaryAdmission.threshold n ≤ f x at hx'
    rw [hz x hxD] at hx'
    exact (not_le_of_gt (BoundaryAdmission.threshold_pos n)) hx'
  refine ⟨?_, isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (hsub.trans Ioo_subset_Icc_self), hsub⟩
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · exact (BoundaryAdmission.truncation_contDiff n).contDiffAt.comp x
      ((hs x hx).contDiffAt (isOpen_Ioo.mem_nhds hx))
  · have hu0 : f x = 0 := hz x hx
    have hevent : ∀ᶠ y in 𝓝 x, f y < BoundaryAdmission.threshold n :=
      hc.continuousAt.eventually_lt continuous_const.continuousAt
        (by rw [hu0]; exact BoundaryAdmission.threshold_pos n)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hevent] with y hy
    exact BoundaryAdmission.truncation_zero_of_le n hy.le

/-- Finite actual real-space difference energy suffices for the original
Fourier form admission of a nonnegative continuous zero extension that is
smooth in the interior. No finite-energy or form-domain premise is used. -/
theorem memRestrictedFormDomain_of_nonnegative_gagliardo
    {f : ℝ → ℝ} (hc : Continuous f)
    (hs : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1))
    (hz : ∀ x ∉ Ioo (-1 : ℝ) 1, f x = 0)
    (hpos : ∀ x, 0 ≤ f x) (hG : gagliardoEnergy f ≠ ∞) :
    MemRestrictedFormDomain f ∧
      energy f f ≤ (gagliardoEnergy f).toReal / gagliardoSymbolConstant := by
  let v : ℕ → ℝ → ℝ := fun n x => BoundaryAdmission.truncation n (f x)
  have hv (n : ℕ) : IsCore (v n) := positiveLevelTruncation_isCore hc hs hz n
  have hfc : HasCompactSupport f := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    exact hz x (fun h => hx (Ioo_subset_Icc_self h))
  have hf : MemLp f 2 volume := hc.memLp_of_hasCompactSupport hfc
  have hL : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0) := by
    apply Torsion.tendsto_eLpNorm_two_of_dominated (B := fun x => 2 * ‖f x‖)
    · intro n
      exact (hv n).1.continuous.aestronglyMeasurable.sub hf.1
    · convert hf.integrable_sq.const_mul (4 : ℝ) using 1
      funext x
      rw [Real.norm_eq_abs, mul_pow, sq_abs]
      norm_num
    · intro n
      exact ae_of_all _ fun x => (norm_sub_le _ _).trans (by
        have hn := BoundaryAdmission.truncation_norm_le (hpos x) n
        change ‖BoundaryAdmission.truncation n (f x)‖ + ‖f x‖ ≤ 2 * ‖f x‖
        rw [Real.norm_of_nonneg (hpos x)]
        linarith)
    · exact ae_of_all _ fun x => by
        simpa only [v, sub_self] using
          (BoundaryAdmission.truncation_tendsto (hpos x)).sub_const (f x)
  have hB (n : ℕ) : energy (v n) (v n) ≤
      (gagliardoEnergy f).toReal / gagliardoSymbolConstant := by
    apply (le_div_iff₀ gagliardoSymbolConstant_pos).2
    have hLip (x y : ℝ) :
        |BoundaryAdmission.truncation n x - BoundaryAdmission.truncation n y| ≤ |x - y| := by
      have h := (SmoothPositivePart.approx_lipschitz n).dist_le_mul
        (x - BoundaryAdmission.threshold n) (y - BoundaryAdmission.threshold n)
      simpa only [BoundaryAdmission.truncation, NNReal.coe_one, one_mul,
        Real.dist_eq, sub_sub_sub_cancel_right] using h
    have h := gagliardoEnergy_comp_le (f := f) hLip
    rw [gagliardoEnergy_of_core (hv n).1 (hv n).2.1] at h
    have hreal := (ENNReal.ofReal_le_iff_le_toReal hG).1 h
    simpa only [v, mul_comm] using hreal
  exact memRestrictedFormDomain_of_core_bounded_energy hf hv hL (Eventually.of_forall hB)

end Torsion.Spectral

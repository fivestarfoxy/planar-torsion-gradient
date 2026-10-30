import Torsion.RestrictedSpectralDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Reflection symmetry of the concrete restricted Fourier problem

Reflection acts on the actual Fourier integral and preserves the defining
smooth-core closure. Consequently every supplied weak eigenfunction can be
reflected without changing its eigenvalue. This does not select the second
eigenvalue or assume simplicity of its eigenspace.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff FourierTransform

namespace Torsion.Spectral

/-- Reflection changes the sign of the frequency in the source's Fourier
convention. No integrability hypothesis is needed for the total integral. -/
theorem fourier_reflect (f : ℝ → ℝ) (ξ : ℝ) :
    fourier (fun x => f (-x)) ξ = fourier f (-ξ) := by
  unfold fourier
  rw [← integral_neg_eq_self (fun x : ℝ =>
    Complex.exp (-((x * -ξ : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) volume]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by simp

/-- Simultaneous reflection preserves the concrete bilinear Fourier form. -/
theorem energy_reflect (f g : ℝ → ℝ) :
    energy (fun x => f (-x)) (fun x => g (-x)) = energy f g := by
  unfold energy
  simp only [fourier_reflect]
  congr 1
  simpa only [abs_neg] using integral_neg_eq_self
    (fun ξ : ℝ => |ξ| * (fourier f ξ * star (fourier g ξ)).re) volume

/-- Reflection can be moved between the arguments of the bilinear form. -/
theorem energy_reflect_left (f g : ℝ → ℝ) :
    energy (fun x => f (-x)) g = energy f (fun x => g (-x)) := by
  simpa only [neg_neg] using energy_reflect f (fun x => g (-x))

theorem FiniteEnergy.reflect {f : ℝ → ℝ} (hf : FiniteEnergy f) :
    FiniteEnergy (fun x => f (-x)) := by
  simpa only [FiniteEnergy, fourier_reflect, abs_neg] using (show Integrable (fun ξ : ℝ => |ξ| * ‖fourier f ξ‖ ^ 2) volume from hf).comp_neg

/-- Reflecting a compact smooth test preserves its support inside the
symmetric interval. -/
theorem IsCore.reflect {f : ℝ → ℝ} (hf : IsCore f) :
    IsCore (fun x => f (-x)) := by
  refine ⟨hf.1.comp contDiff_neg, hf.2.1.comp_homeomorph (Homeomorph.neg ℝ), ?_⟩
  have hsub : tsupport (fun x => f (-x)) ⊆ (fun x : ℝ => -x) ⁻¹' tsupport f := by
    apply closure_minimal
    · intro x hx
      exact subset_closure hx
    · exact (isClosed_tsupport f).preimage continuous_neg
  intro x hx
  have h := hf.2.2 (hsub hx)
  change -1 < -x ∧ -x < 1 at h
  constructor <;> linarith [h.1, h.2]

/-- Reflection preserves the actual restricted form domain, including its
core approximation in both L² and half-derivative energy. -/
theorem MemRestrictedFormDomain.reflect {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) : MemRestrictedFormDomain (fun x => f (-x)) := by
  rcases hf with ⟨hlp, he, hz, v, hv, hvlp, hve⟩
  refine ⟨hlp.comp_measurePreserving (Measure.measurePreserving_neg volume), he.reflect,
    ?_, (fun n x => v n (-x)), (fun n => (hv n).reflect), ?_, ?_⟩
  · have hz' := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hz
    filter_upwards [hz'] with x hx hnot
    apply hx
    intro hmem
    apply hnot
    constructor <;> linarith [hmem.1, hmem.2]
  · convert hvlp using 1
    funext n
    change eLpNorm ((fun x => v n x - f x) ∘ (fun x => -x)) 2 volume = _
    exact eLpNorm_comp_measurePreserving
      (((hv n).1.continuous.aestronglyMeasurable).sub hlp.1)
      (Measure.measurePreserving_neg volume)
  · convert hve using 1
    funext n
    exact energy_reflect (fun x => v n x - f x) (fun x => v n x - f x)

/-- The weak restricted eigenvalue equation is equivariant under reflection.
The reflected function is nonzero as an L² class. -/
theorem IsRestrictedEigenfunction.reflect {a : ℝ} {φ : ℝ → ℝ}
    (hφ : IsRestrictedEigenfunction a φ) :
    IsRestrictedEigenfunction a (fun x => φ (-x)) := by
  refine ⟨hφ.1.reflect, ?_, ?_⟩
  · intro hz
    have hz' := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hz
    exact hφ.2.1 (by simpa only [neg_neg] using hz')
  · intro ψ hψ
    rw [energy_reflect_left, hφ.2.2 _ hψ.reflect]
    congr 1
    simpa only [neg_neg] using integral_neg_eq_self
      (fun x : ℝ => φ x * ψ (-x)) volume |>.symm

/-- The defining smooth core is closed under addition. -/
theorem IsCore.add {f g : ℝ → ℝ} (hf : IsCore f) (hg : IsCore g) :
    IsCore (fun x => f x + g x) :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    tsupport_add.trans (union_subset hf.2.2 hg.2.2)⟩

/-- Scalar multiplication preserves the actual smooth core. -/
theorem IsCore.const_mul {f : ℝ → ℝ} (hf : IsCore f) (c : ℝ) :
    IsCore (fun x => c * f x) := by
  exact ⟨contDiff_const.mul hf.1, hf.2.1.mul_left,
    tsupport_mul_subset_right.trans hf.2.2⟩

/-- A direct bound on the actual diagonal form used to add approximants. -/
theorem energy_add_self_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hef : FiniteEnergy f) (heg : FiniteEnergy g) :
    energy (fun x => f x + g x) (fun x => f x + g x) ≤
      2 * energy f f + 2 * energy g g := by
  simp only [energy_self, fourier_add hf hg, Pi.add_apply]
  have hi : (∫ ξ : ℝ, |ξ| * ‖fourier f ξ + fourier g ξ‖ ^ 2) ≤
      ∫ ξ : ℝ, 2 * (|ξ| * ‖fourier f ξ‖ ^ 2) +
        2 * (|ξ| * ‖fourier g ξ‖ ^ 2) := by
    have hsum : Integrable (fun ξ : ℝ => |ξ| * ‖fourier f ξ + fourier g ξ‖ ^ 2) := by
      simpa only [FiniteEnergy, fourier_add hf hg, Pi.add_apply] using
        FiniteEnergy.add hf hg hef heg
    apply integral_mono hsum
      (((show Integrable (fun ξ : ℝ => |ξ| * ‖fourier f ξ‖ ^ 2) volume from hef).const_mul 2).add
        ((show Integrable (fun ξ : ℝ => |ξ| * ‖fourier g ξ‖ ^ 2) volume from heg).const_mul 2))
    intro ξ
    change |ξ| * ‖fourier f ξ + fourier g ξ‖ ^ 2 ≤
      2 * (|ξ| * ‖fourier f ξ‖ ^ 2) + 2 * (|ξ| * ‖fourier g ξ‖ ^ 2)
    have hn := norm_add_le (fourier f ξ) (fourier g ξ)
    have hs : ‖fourier f ξ + fourier g ξ‖ ^ 2 ≤
        2 * ‖fourier f ξ‖ ^ 2 + 2 * ‖fourier g ξ‖ ^ 2 := by
      nlinarith [sq_nonneg (‖fourier f ξ‖ - ‖fourier g ξ‖),
        norm_nonneg (fourier f ξ + fourier g ξ)]
    nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg ξ)]
  rw [integral_add
    ((show Integrable (fun ξ : ℝ => |ξ| * ‖fourier f ξ‖ ^ 2) volume from hef).const_mul 2)
    ((show Integrable (fun ξ : ℝ => |ξ| * ‖fourier g ξ‖ ^ 2) volume from heg).const_mul 2),
    integral_const_mul, integral_const_mul] at hi
  nlinarith [mul_le_mul_of_nonneg_left hi (by positivity :
    0 ≤ (1 / (2 * Real.pi) : ℝ))]

/-- Exact scaling of the actual diagonal form. -/
theorem energy_const_mul_self (c : ℝ) (f : ℝ → ℝ) :
    energy (fun x => c * f x) (fun x => c * f x) = c ^ 2 * energy f f := by
  simp only [energy_self, fourier_const_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  have heq : (fun ξ : ℝ => |ξ| * (c ^ 2 * ‖fourier f ξ‖ ^ 2)) =
      fun ξ => c ^ 2 * (|ξ| * ‖fourier f ξ‖ ^ 2) := by funext ξ; ring
  rw [heq, integral_const_mul]
  ring

/-- Addition preserves the defining restricted form closure. -/
theorem MemRestrictedFormDomain.add {f g : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hg : MemRestrictedFormDomain g) :
    MemRestrictedFormDomain (fun x => f x + g x) := by
  have hfi := hf.integrable
  have hgi := hg.integrable
  rcases hf with ⟨hflp, hfe, hfz, v, hv, hvlp, hve⟩
  rcases hg with ⟨hglp, hge, hgz, w, hw, hwlp, hwe⟩
  refine ⟨hflp.add hglp, FiniteEnergy.add hfi hgi hfe hge, ?_,
    (fun n x => v n x + w n x), (fun n => (hv n).add (hw n)), ?_, ?_⟩
  · filter_upwards [hfz, hgz] with x hfx hgx hx
    rw [hfx hx, hgx hx, add_zero]
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hvlp.add hwlp)
    · intro n
      exact zero_le _
    · intro n
      have heq : (fun x => v n x + w n x - (f x + g x)) =
          fun x => (v n x - f x) + (w n x - g x) := by funext x; ring
      dsimp only
      rw [heq]
      exact eLpNorm_add_le
        (((hv n).1.continuous.aestronglyMeasurable).sub hflp.1)
        (((hw n).1.continuous.aestronglyMeasurable).sub hglp.1) (by norm_num)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using (hve.const_mul 2).add (hwe.const_mul 2))
    · intro n
      exact energy_nonneg _
    · intro n
      have hvi := (hv n).memRestrictedFormDomain.integrable
      have hwi := (hw n).memRestrictedFormDomain.integrable
      have hve' : FiniteEnergy (fun x => v n x - f x) := by
        simpa only [sub_eq_add_neg, neg_one_mul] using
          (FiniteEnergy.add hvi (hfi.const_mul (-1)) (hv n).memRestrictedFormDomain.2.1
            (FiniteEnergy.const_mul hfi hfe (-1)))
      have hwe' : FiniteEnergy (fun x => w n x - g x) := by
        simpa only [sub_eq_add_neg, neg_one_mul] using
          (FiniteEnergy.add hwi (hgi.const_mul (-1)) (hw n).memRestrictedFormDomain.2.1
            (FiniteEnergy.const_mul hgi hge (-1)))
      have heq : (fun x => v n x + w n x - (f x + g x)) =
          fun x => (v n x - f x) + (w n x - g x) := by funext x; ring
      dsimp only
      rw [heq]
      exact energy_add_self_le (hvi.sub hfi) (hwi.sub hgi) hve' hwe'

/-- Scalar multiplication preserves both approximation limits in the actual
restricted form domain. -/
theorem MemRestrictedFormDomain.const_mul {f : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (c : ℝ) :
    MemRestrictedFormDomain (fun x => c * f x) := by
  have hfi := hf.integrable
  rcases hf with ⟨hlp, he, hz, v, hv, hvlp, hve⟩
  refine ⟨hlp.const_mul c, FiniteEnergy.const_mul hfi he c, ?_,
    (fun n x => c * v n x), (fun n => (hv n).const_mul c), ?_, ?_⟩
  · filter_upwards [hz] with x hx hx'
    rw [hx hx', mul_zero]
  · have heq (n : ℕ) : (fun x => c * v n x - c * f x) =
        c • (fun x => v n x - f x) := by funext x; simp; ring
    simp_rw [heq, eLpNorm_const_smul]
    simpa using ENNReal.Tendsto.const_mul hvlp (Or.inr (enorm_ne_top (x := c)))
  · have heq (n : ℕ) : (fun x => c * v n x - c * f x) =
        fun x => c * (v n x - f x) := by funext x; ring
    simp_rw [heq, energy_const_mul_self]
    simpa using hve.const_mul (c ^ 2)

/-- Any nonzero linear combination of supplied eigenfunctions in the same
actual eigenspace again satisfies the restricted weak equation. -/
theorem IsRestrictedEigenfunction.linear_combination {a c d : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : IsRestrictedEigenfunction a φ) (hψ : IsRestrictedEigenfunction a ψ)
    (hne : ¬ (fun x => c * φ x + d * ψ x) =ᵐ[volume] 0) :
    IsRestrictedEigenfunction a (fun x => c * φ x + d * ψ x) := by
  refine ⟨(hφ.1.const_mul c).add (hψ.1.const_mul d), hne, ?_⟩
  intro η hη
  have hc := hφ.1.const_mul c
  have hd := hψ.1.const_mul d
  rw [energy_add_left hc.integrable hd.integrable hη.integrable hc.2.1 hd.2.1 hη.2.1,
    energy_const_mul_left, energy_const_mul_left,
    hφ.2.2 η hη, hψ.2.2 η hη]
  have heq : (fun x => (c * φ x + d * ψ x) * η x) =
      fun x => c * (φ x * η x) + d * (ψ x * η x) := by funext x; ring
  rw [heq, integral_add ((hφ.1.integrable_mul hη).const_mul c)
    ((hψ.1.integrable_mul hη).const_mul d), integral_const_mul, integral_const_mul]
  ring

/-- A supplied nonzero eigenspace contains an actual even or odd nonzero
weak eigenfunction, obtained from reflection. This proves a parity
reduction, but does not decide which parity belongs to the second eigenvalue. -/
theorem IsRestrictedEigenfunction.exists_even_or_odd {a : ℝ} {φ : ℝ → ℝ}
    (hφ : IsRestrictedEigenfunction a φ) :
    ∃ ψ : ℝ → ℝ, IsRestrictedEigenfunction a ψ ∧
      (Function.Even ψ ∨ Function.Odd ψ) := by
  by_cases he : (fun x => φ x + φ (-x)) =ᵐ[volume] 0
  · have ho : ¬ (fun x => φ x - φ (-x)) =ᵐ[volume] 0 := by
      intro ho
      apply hφ.2.1
      filter_upwards [he, ho] with x hx hy
      change φ x + φ (-x) = 0 at hx
      change φ x - φ (-x) = 0 at hy
      linarith
    refine ⟨(fun x => φ x - φ (-x)), ?_, Or.inr ?_⟩
    · simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg] using
        hφ.linear_combination (c := 1) (d := -1) hφ.reflect (by
          simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg] using ho)
    · intro x
      simp only [neg_neg]
      ring
  · refine ⟨(fun x => φ x + φ (-x)), ?_, Or.inl ?_⟩
    · simpa only [one_mul] using
        hφ.linear_combination (c := 1) (d := 1) hφ.reflect (by simpa only [one_mul] using he)
    · intro x
      simp only [neg_neg]
      ring

/-- The even and odd subspaces are orthogonal for the concrete half-energy
form, not only for the L² pairing. -/
theorem energy_eq_zero_of_even_odd {f g : ℝ → ℝ}
    (hf : Function.Even f) (hg : Function.Odd g) : energy f g = 0 := by
  have h := energy_reflect f g
  have he : (fun x => f (-x)) = f := funext hf
  have ho : (fun x => g (-x)) = (fun x => (-1 : ℝ) * g x) := by
    funext x
    simp only [hg x, neg_one_mul]
  rw [he, ho, energy_symm, energy_const_mul_left, energy_symm] at h
  linarith

/-- The L² pairing between an even and an odd real function is zero.
The total integral formulation includes the nonintegrable case as well. -/
theorem integral_mul_eq_zero_of_even_odd {f g : ℝ → ℝ}
    (hf : Function.Even f) (hg : Function.Odd g) :
    (∫ x : ℝ, f x * g x) = 0 := by
  have h := integral_neg_eq_self (fun x : ℝ => f x * g x) volume
  have heq : (fun x : ℝ => f (-x) * g (-x)) = fun x => -(f x * g x) := by
    funext x
    rw [hf x, hg x, mul_neg]
  rw [heq, integral_neg] at h
  linarith

/-- The actual form ignores changes of representatives on null sets. -/
theorem energy_congr_ae {f f' g g' : ℝ → ℝ}
    (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    energy f g = energy f' g' := by
  unfold energy
  rw [fourier_congr_ae hf, fourier_congr_ae hg]

/-- The full defining core closure descends to L² equivalence classes. -/
theorem MemRestrictedFormDomain.congr_ae {f g : ℝ → ℝ}
    (hf : MemRestrictedFormDomain f) (hfg : f =ᵐ[volume] g) :
    MemRestrictedFormDomain g := by
  rcases hf with ⟨hlp, he, hz, v, hv, hvlp, hve⟩
  refine ⟨(memLp_congr_ae hfg).mp hlp, ?_, ?_, v, hv, ?_, ?_⟩
  · unfold FiniteEnergy at he ⊢
    rwa [← fourier_congr_ae hfg]
  · filter_upwards [hz, hfg] with x hx hfx hx'
    rw [← hfx]
    exact hx hx'
  · convert hvlp using 1
    funext n
    exact eLpNorm_congr_ae (by filter_upwards [hfg] with x hx; simp only [hx])
  · convert hve using 1
    funext n
    apply energy_congr_ae <;>
      filter_upwards [hfg] with x hx <;> simp only [hx]

/-- Replacing a supplied eigenfunction by an a.e. equal representative
preserves its actual weak equation and its nonzero L² class. -/
theorem IsRestrictedEigenfunction.congr_ae {a : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : IsRestrictedEigenfunction a φ) (hφψ : φ =ᵐ[volume] ψ) :
    IsRestrictedEigenfunction a ψ := by
  refine ⟨hφ.1.congr_ae hφψ, (fun hz => hφ.2.1 (hφψ.trans hz)), ?_⟩
  intro η hη
  rw [← energy_congr_ae hφψ (Filter.EventuallyEq.rfl), hφ.2.2 η hη]
  congr 1
  exact integral_congr_ae (by filter_upwards [hφψ] with x hx; simp only [hx])

end Torsion.Spectral

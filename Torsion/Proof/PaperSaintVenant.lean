module

public import Torsion.Proof.PaperUniformLoad
public import Torsion.Proof.PaperGradientPositive

@[expose] public section

/-! # Prescribed twist and prescribed torque for a Saint-Venant bar -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Torsion.DirichletTheory

/-- Testing with the solution expresses the integral of deflection as
energy. Unit forcing makes this quantity strictly positive. -/
theorem integral_torsion_pos (T : DirichletTheory) (D : ConvexDomain) :
    0 < ∫ x in D.carrier, (T.solution D).value x := by
  let u := T.solution D
  have heq := u.weakEquation.2 u.value u.weakGradient u.weakEquation.1
  rw [← heq]
  have hn : 0 ≤ᵐ[volume.restrict D.carrier] fun x =>
      inner (𝕜 := ℝ) (u.weakGradient x) (u.weakGradient x) :=
    Filter.Eventually.of_forall fun x => real_inner_self_nonneg
  refine lt_of_le_of_ne (integral_nonneg_of_ae hn) ?_
  intro hz
  have hi := integrable_real_inner_of_memLp_two (u.weakEquation.1.2.1.restrict D.carrier)
    (u.weakEquation.1.2.1.restrict D.carrier)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz.symm
  have hg : u.weakGradient =ᵐ[volume.restrict D.carrier] 0 := by
    filter_upwards [hzero] with x hx
    exact inner_self_eq_zero.mp hx
  exact (T.G_pos D).ne' ((eLpNorm_eq_zero_iff (by norm_num : (∞ : ℝ≥0∞) ≠ 0)).mpr hg)

/-- The peak magnitude of the shear field, obtained by turning the
gradient of the Prandtl stress function through a right angle. -/
theorem peak_shear_of_stress_factor (T : DirichletTheory) (D : ConvexDomain) (s : ℝ) :
    eLpNorm (fun x => (-Complex.I * (s : ℂ)) • (T.solution D).weakGradient x)
      ∞ (volume.restrict D.carrier) = ENNReal.ofReal |s| * T.G D := by
  change eLpNorm ((-Complex.I * (s : ℂ)) • (T.solution D).weakGradient) _ _ = _
  rw [eLpNorm_const_smul, ← ofReal_norm]
  simp [Complex.norm_real, Real.norm_eq_abs, G]

/-- Fixing the twist gives peak stress 2μ|α| G(D). -/
theorem peak_shear_prescribed_twist (T : DirichletTheory) (D : ConvexDomain)
    (μ α : ℝ) (hμ : 0 < μ) :
    eLpNorm (fun x => (-Complex.I * ((2*μ*α : ℝ) : ℂ)) • (T.solution D).weakGradient x)
      ∞ (volume.restrict D.carrier) = ENNReal.ofReal (2*μ*|α|) * T.G D := by
  rw [T.peak_shear_of_stress_factor, abs_mul, abs_of_pos (by positivity : 0 < 2*μ)]

/-- Prescribed torque equals twice the area integral of the Prandtl
stress function. Solving this relation gives the peak for that torque. -/
theorem peak_shear_prescribed_torque (T : DirichletTheory) (D : ConvexDomain)
    (s torque : ℝ) (ht : torque = 2 * ∫ x in D.carrier, s * (T.solution D).value x) :
    eLpNorm (fun x => (-Complex.I * (s : ℂ)) • (T.solution D).weakGradient x)
      ∞ (volume.restrict D.carrier) =
      ENNReal.ofReal (|torque| / (2 * ∫ x in D.carrier, (T.solution D).value x)) * T.G D := by
  have hi := T.integral_torsion_pos D
  rw [T.peak_shear_of_stress_factor, ht, integral_const_mul, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hi]
  congr 2
  field_simp

end Torsion.DirichletTheory

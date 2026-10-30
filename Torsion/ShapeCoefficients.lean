module

public import Torsion.Definitions
public import Torsion.ShapeDeformation
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Concrete planar coefficients for localized shape calculus

These are the actual determinant and inverse-Jacobian coefficients of
`id + t V`, in the real basis `(1,I)`. Their first variations are proved
directly, including the matrix `(div V) I - DV - DVᵀ` of the fixed-domain
Dirichlet energy. They do not assert transport or a shape derivative of a
weak torsion solution.
-/

noncomputable section
open Set Filter
open scoped Topology Matrix ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Torsion.Shape

abbrev RealMatrix := Matrix (Fin 2) (Fin 2) ℝ

/-- Real matrix of a genuine planar differential in the physical basis. -/
def realMatrix (L : Plane →L[ℝ] Plane) : RealMatrix :=
  LinearMap.toMatrix Complex.basisOneI Complex.basisOneI L.toLinearMap

/-- The actual derivative matrix of `id + t V` when `B = DV`. -/
def deformationMatrix (B : RealMatrix) (t : ℝ) : RealMatrix := 1 + t • B

/-- The physical Jacobian, rather than a separately assigned scalar. -/
def jacobian (B : RealMatrix) (t : ℝ) : ℝ := (deformationMatrix B t).det

/-- The fixed-domain gradient-energy coefficient `J DT⁻¹ DT⁻ᵀ`. -/
def energyMatrix (B : RealMatrix) (t : ℝ) : RealMatrix :=
  jacobian B t • ((deformationMatrix B t)⁻¹ * ((deformationMatrix B t)⁻¹)ᵀ)

/-- The expected first variation of the actual energy coefficient. -/
def energyVariation (B : RealMatrix) : RealMatrix := Matrix.trace B • 1 - B - Bᵀ

@[simp] theorem deformationMatrix_zero (B : RealMatrix) : deformationMatrix B 0 = 1 := by
  simp [deformationMatrix]

@[simp] theorem jacobian_zero (B : RealMatrix) : jacobian B 0 = 1 := by
  simp [jacobian]

@[simp] theorem energyMatrix_zero (B : RealMatrix) : energyMatrix B 0 = 1 := by
  simp [energyMatrix]

/-- Exact quadratic Jacobian polynomial in dimension two. -/
theorem jacobian_polynomial (B : RealMatrix) (t : ℝ) :
    jacobian B t = 1 + t * Matrix.trace B + t ^ 2 * B.det := by
  simp [jacobian, deformationMatrix, Matrix.det_fin_two, Matrix.trace, Fin.sum_univ_two]
  ring

theorem jacobian_hasDerivAt (B : RealMatrix) (t : ℝ) :
    HasDerivAt (jacobian B) (Matrix.trace B + 2 * t * B.det) t := by
  have h := ((hasDerivAt_const t (1 : ℝ)).add
    ((hasDerivAt_id t).mul_const (Matrix.trace B))).add
    (((hasDerivAt_id t).pow 2).mul_const B.det)
  convert h using 1
  · funext s
    exact jacobian_polynomial B s
  · simp

theorem jacobian_hasDerivAt_zero (B : RealMatrix) :
    HasDerivAt (jacobian B) (Matrix.trace B) 0 := by
  simpa using jacobian_hasDerivAt B 0

theorem jacobian_pos_near_zero (B : RealMatrix) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < jacobian B t := by
  have hc := (jacobian_hasDerivAt_zero B).continuousAt
  exact (continuous_const.continuousAt.eventually_lt hc (by simp)).mono fun _ h => h

/-- Exact adjugate formula for the actual inverse matrix. -/
theorem inverse_deformationMatrix_explicit (B : RealMatrix) (t : ℝ) :
    (deformationMatrix B t)⁻¹ = (jacobian B t)⁻¹ •
      !![1 + t * B 1 1, -(t * B 0 1); -(t * B 1 0), 1 + t * B 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.inv_def, Matrix.adjugate_fin_two, deformationMatrix, jacobian]

/-- The coefficient is an ordinary rational matrix on the invertible range. -/
theorem energyMatrix_explicit (B : RealMatrix) {t : ℝ} (hJ : jacobian B t ≠ 0) :
    energyMatrix B t =
      !![((1 + t * B 1 1) ^ 2 + (t * B 0 1) ^ 2) / jacobian B t,
          -(t * B 1 0 * (1 + t * B 1 1) + t * B 0 1 * (1 + t * B 0 0)) / jacobian B t;
          -(t * B 1 0 * (1 + t * B 1 1) + t * B 0 1 * (1 + t * B 0 0)) / jacobian B t,
          ((t * B 1 0) ^ 2 + (1 + t * B 0 0) ^ 2) / jacobian B t] := by
  rw [energyMatrix, inverse_deformationMatrix_explicit]
  ext i j
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
    smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp [hJ] <;> ring

/-- The actual inverse-Jacobian coefficient has the Hadamard first variation. -/
theorem energyMatrix_hasDerivAt_zero (B : RealMatrix) :
    HasDerivAt (energyMatrix B) (energyVariation B) 0 := by
  let P : ℝ → RealMatrix := fun t =>
    !![((1 + t * B 1 1) ^ 2 + (t * B 0 1) ^ 2) / jacobian B t,
        -(t * B 1 0 * (1 + t * B 1 1) + t * B 0 1 * (1 + t * B 0 0)) / jacobian B t;
        -(t * B 1 0 * (1 + t * B 1 1) + t * B 0 1 * (1 + t * B 0 0)) / jacobian B t,
        ((t * B 1 0) ^ 2 + (1 + t * B 0 0) ^ 2) / jacobian B t]
  have hJ := jacobian_hasDerivAt_zero B
  have hdiag (p q : ℝ) : HasDerivAt
      (fun t => ((1 + t * p) ^ 2 + (t * q) ^ 2) / jacobian B t)
      (2 * p - Matrix.trace B) 0 := by
    have h := ((((hasDerivAt_const 0 (1 : ℝ)).add
      ((hasDerivAt_id 0).mul_const p)).pow 2).add
      (((hasDerivAt_id 0).mul_const q).pow 2)).div hJ (by simp)
    convert h using 1 <;> simp
    funext t
    rfl
  have hoff : HasDerivAt
      (fun t => -(t * B 1 0 * (1 + t * B 1 1) +
        t * B 0 1 * (1 + t * B 0 0)) / jacobian B t)
      (-(B 1 0 + B 0 1)) 0 := by
    have h := ((((hasDerivAt_id 0).mul_const (B 1 0)).mul
      ((hasDerivAt_const 0 (1 : ℝ)).add ((hasDerivAt_id 0).mul_const (B 1 1)))).add
      (((hasDerivAt_id 0).mul_const (B 0 1)).mul
        ((hasDerivAt_const 0 (1 : ℝ)).add ((hasDerivAt_id 0).mul_const (B 0 0))))).neg.div
        hJ (by simp)
    convert h using 1 <;> simp
    funext t
    rfl
  have hP : HasDerivAt P (energyVariation B) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j
    · convert hdiag (B 1 1) (B 0 1) using 1 <;>
        simp [P, energyVariation, Matrix.trace, Fin.sum_univ_two] <;> ring
    · convert hoff using 1 <;> simp [P, energyVariation, Matrix.trace, Fin.sum_univ_two] <;> ring
    · convert hoff using 1 <;> simp [P, energyVariation, Matrix.trace, Fin.sum_univ_two] <;> ring
    · convert hdiag (B 0 0) (B 1 0) using 1
      · funext t
        simp [P]
        ring
      · simp [energyVariation, Matrix.trace, Fin.sum_univ_two]
        ring
  have heq : energyMatrix B =ᶠ[𝓝 0] P := by
    filter_upwards [jacobian_pos_near_zero B] with t ht
    exact energyMatrix_explicit B ht.ne'
  exact hP.congr_of_eventuallyEq heq

/-- The matrix determinant is the Jacobian of the actual planar deformation. -/
theorem det_fderiv_deformation {V : Plane → Plane} {z : Plane}
    (hV : DifferentiableAt ℝ V z) (t : ℝ) :
    LinearMap.det (fderiv ℝ (deformation V t) z).toLinearMap =
      jacobian (realMatrix (fderiv ℝ V z)) t := by
  change LinearMap.det (fderiv ℝ (fun w : Plane => w + t • V w) z).toLinearMap = _
  have hd := (hasFDerivAt_id z).add (hV.hasFDerivAt.const_smul t)
  change HasFDerivAt (fun w : Plane => w + t • V w) _ z at hd
  rw [hd.fderiv]
  change LinearMap.det (LinearMap.id + t • (fderiv ℝ V z).toLinearMap) = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  rw [map_add, map_smul, LinearMap.toMatrix_id]
  rfl

/-- Identification of the full matrix with the actual spatial differential. -/
theorem realMatrix_fderiv_deformation {V : Plane → Plane} {z : Plane}
    (hV : DifferentiableAt ℝ V z) (t : ℝ) :
    realMatrix (fderiv ℝ (deformation V t) z) =
      deformationMatrix (realMatrix (fderiv ℝ V z)) t := by
  rw [(deformation_hasFDerivAt hV t).fderiv]
  change LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
    (LinearMap.id + t • (fderiv ℝ V z).toLinearMap) = _
  rw [map_add, map_smul, LinearMap.toMatrix_id]
  rfl

/-- Divergence in physical Cartesian coordinates. -/
def divergence (V : Plane → Plane) (z : Plane) : ℝ :=
  (fderiv ℝ V z (1 : Plane)).re + (fderiv ℝ V z Complex.I).im

theorem trace_realMatrix (L : Plane →L[ℝ] Plane) :
    Matrix.trace (realMatrix L) = (L (1 : Plane)).re + (L Complex.I).im := by
  simp [realMatrix, Matrix.trace, Fin.sum_univ_two, LinearMap.toMatrix_apply,
    Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

/-- The physical Jacobian first variation is exactly the actual divergence. -/
theorem physicalJacobian_hasDerivAt_zero {V : Plane → Plane} {z : Plane}
    (hV : DifferentiableAt ℝ V z) :
    HasDerivAt (fun t : ℝ => LinearMap.det
      (fderiv ℝ (deformation V t) z).toLinearMap) (divergence V z) 0 := by
  have heq : (fun t : ℝ => LinearMap.det (fderiv ℝ (deformation V t) z).toLinearMap) =
      jacobian (realMatrix (fderiv ℝ V z)) := by
    funext t
    exact det_fderiv_deformation hV t
  rw [heq, divergence, ← trace_realMatrix]
  exact jacobian_hasDerivAt_zero _

/-- The actual physical coefficient, defined directly through `DT` and `J`. -/
def physicalEnergyMatrix (V : Plane → Plane) (t : ℝ) (z : Plane) : RealMatrix :=
  LinearMap.det (fderiv ℝ (deformation V t) z).toLinearMap •
    ((realMatrix (fderiv ℝ (deformation V t) z))⁻¹ *
      ((realMatrix (fderiv ℝ (deformation V t) z))⁻¹)ᵀ)

theorem physicalEnergyMatrix_eq {V : Plane → Plane} {z : Plane}
    (hV : DifferentiableAt ℝ V z) (t : ℝ) :
    physicalEnergyMatrix V t z = energyMatrix (realMatrix (fderiv ℝ V z)) t := by
  unfold physicalEnergyMatrix energyMatrix
  rw [realMatrix_fderiv_deformation hV t, det_fderiv_deformation hV t]

/-- First variation of the actual physical fixed-domain energy coefficient. -/
theorem physicalEnergyMatrix_hasDerivAt_zero {V : Plane → Plane} {z : Plane}
    (hV : DifferentiableAt ℝ V z) :
    HasDerivAt (fun t : ℝ => physicalEnergyMatrix V t z)
      (energyVariation (realMatrix (fderiv ℝ V z))) 0 := by
  have heq : (fun t : ℝ => physicalEnergyMatrix V t z) =
      energyMatrix (realMatrix (fderiv ℝ V z)) := funext (physicalEnergyMatrix_eq hV)
  rw [heq]
  exact energyMatrix_hasDerivAt_zero _

/-- Coordinate entries of the real differential are controlled by its true
Euclidean operator norm. -/
theorem realMatrix_entry_le_norm (L : Plane →L[ℝ] Plane) (i j : Fin 2) :
    |realMatrix L i j| ≤ ‖L‖ := by
  have h1 : ‖L (1 : Plane)‖ ≤ ‖L‖ := by simpa using L.le_opNorm (1 : Plane)
  have hI : ‖L Complex.I‖ ≤ ‖L‖ := by simpa using L.le_opNorm Complex.I
  fin_cases i <;> fin_cases j <;>
    simp only [realMatrix, LinearMap.toMatrix_apply, Complex.coe_basisOneI,
      Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const] <;>
    first | exact (Complex.abs_re_le_norm _).trans h1
          | exact (Complex.abs_re_le_norm _).trans hI
          | exact (Complex.abs_im_le_norm _).trans h1
          | exact (Complex.abs_im_le_norm _).trans hI

/-- An explicit uniform Jacobian lower bound from a bound on the derivative
entries. This is the positive density needed by Sobolev pullback estimates. -/
theorem abs_jacobian_sub_one_le_half_of_entry_bound (B : RealMatrix) {K t : ℝ}
    (hK : 0 ≤ K) (hB : ∀ i j, |B i j| ≤ K)
    (ht : |t| ≤ 1 / (4 * (K + 1) ^ 2)) :
    |jacobian B t - 1| ≤ 1 / 2 := by
  have hden : 0 < 4 * (K + 1) ^ 2 := by positivity
  have hscale : 4 * |t| * (K + 1) ^ 2 ≤ 1 := by
    have h := (le_div_iff₀ hden).mp ht
    nlinarith
  have ht₁ : |t| ≤ 1 := by
    have hsq : 1 ≤ (K + 1) ^ 2 := by nlinarith
    nlinarith [abs_nonneg t]
  have htr : |Matrix.trace B| ≤ 2 * K := by
    simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply]
    exact (abs_add_le _ _).trans (by linarith [hB 0 0, hB 1 1])
  have hdet : |B.det| ≤ 2 * K ^ 2 := by
    rw [Matrix.det_fin_two]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul]
    have hmul₀ := mul_le_mul (hB 0 0) (hB 1 1) (abs_nonneg _) hK
    have hmul₁ := mul_le_mul (hB 0 1) (hB 1 0) (abs_nonneg _) hK
    nlinarith
  have hsq : t ^ 2 ≤ |t| := by nlinarith [sq_abs t, abs_nonneg t]
  have hrem : |jacobian B t - 1| ≤ |t| * (2 * K) + t ^ 2 * (2 * K ^ 2) := by
    rw [jacobian_polynomial]
    have heq : 1 + t * Matrix.trace B + t ^ 2 * B.det - 1 =
        t * Matrix.trace B + t ^ 2 * B.det := by ring
    rw [heq]
    apply (abs_add_le _ _).trans
    simp only [abs_mul, abs_pow, sq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_left htr (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hdet (sq_nonneg _))
  have hsmall : |t| * (2 * K) + t ^ 2 * (2 * K ^ 2) ≤ 1 / 2 := by
    have hsqmul := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ 2 * K ^ 2)
    nlinarith [abs_nonneg t]
  exact hrem.trans hsmall

theorem jacobian_half_le_of_entry_bound (B : RealMatrix) {K t : ℝ}
    (hK : 0 ≤ K) (hB : ∀ i j, |B i j| ≤ K)
    (ht : |t| ≤ 1 / (4 * (K + 1) ^ 2)) :
    1 / 2 ≤ jacobian B t := by
  have h := (abs_le.mp (abs_jacobian_sub_one_le_half_of_entry_bound B hK hB ht)).1
  linarith

theorem jacobian_le_three_halves_of_entry_bound (B : RealMatrix) {K t : ℝ}
    (hK : 0 ≤ K) (hB : ∀ i j, |B i j| ≤ K)
    (ht : |t| ≤ 1 / (4 * (K + 1) ^ 2)) :
    jacobian B t ≤ 3 / 2 := by
  have h := (abs_le.mp (abs_jacobian_sub_one_le_half_of_entry_bound B hK hB ht)).2
  linarith

/-- Every actual smooth compactly supported planar deformation has a common
parameter interval where its physical Jacobian is bounded below by one half
at every point. There is no pointwise radius or unproved density premise. -/
theorem exists_uniform_jacobian_bounds {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ z : Plane,
      1 / 2 ≤ LinearMap.det (fderiv ℝ (deformation V t) z).toLinearMap ∧
      LinearMap.det (fderiv ℝ (deformation V t) z).toLinearMap ≤ 3 / 2 := by
  obtain ⟨C, hC⟩ := (hVc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hV.continuous_fderiv (by simp))
  let K := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  refine ⟨1 / (4 * (K + 1) ^ 2), by positivity, ?_⟩
  intro t ht z
  rw [det_fderiv_deformation ((hV.differentiable (by simp)) z) t]
  have hb (i j : Fin 2) : |realMatrix (fderiv ℝ V z) i j| ≤ K :=
    (realMatrix_entry_le_norm _ i j).trans ((hC z).trans (le_max_left _ _))
  exact ⟨jacobian_half_le_of_entry_bound _ hK hb ht.le,
    jacobian_le_three_halves_of_entry_bound _ hK hb ht.le⟩

/-- Uniform positive Jacobian bound, as a convenient single-sided corollary. -/
theorem exists_uniform_jacobian_half_le {V : Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ z : Plane,
      1 / 2 ≤ LinearMap.det (fderiv ℝ (deformation V t) z).toLinearMap := by
  obtain ⟨δ, hδ, hbounds⟩ := exists_uniform_jacobian_bounds hV hVc
  exact ⟨δ, hδ, fun t ht z => (hbounds t ht z).1⟩

end Torsion.Shape

import Torsion.Definitions
import Torsion.Moments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Conditional exact value and attainment

This is the last step of Theorem 1.1, over the concrete weak-solution and
essential-supremum definitions in `Definitions`. The low-level analytic
inputs are explicit arguments: the scaling law, a reference domain with
its exact area and marked-flux lower bound, and the global calibration
inequality. `ProvedMain` constructs the weak theory and scaling law; its
remaining reference certificate is still unconstructed. This is NOT an unconditional proof of
Theorem 1.1 or of the spectral construction.
-/

noncomputable section
open Set

namespace Torsion

/-- The domain scaling and PDE scaling conclusions of Lemma 2.3.
`carrier_eq` ensures this operation is physical dilation, not an unrelated
operation on domain labels. This structure is an explicit hypothesis. -/
structure ScalingLaw (T : DirichletTheory) where
  domain : (s : ℝ) → 0 < s → ConvexDomain → ConvexDomain
  carrier_eq : ∀ s hs D, (domain s hs D).carrier =
    (fun z : ℂ => (s : ℂ) * z) '' D.carrier
  area_eq : ∀ s hs D, (domain s hs D).area = s ^ 2 * D.area
  gradient_eq : ∀ s hs D, T.G (domain s hs D) = ENNReal.ofReal s * T.G D

/-- The analytic output needed from Sections 4--7.

The `universal` field is precisely the global calibration/convex-extension
obligation. The other fields identify the area and supply the lower bound
from interior gradients approaching the marked point. None of these fields
is manufactured from scalar moment algebra. -/
structure ReferenceCertificate (T : DirichletTheory) (d : Moments) where
  domain : ConvexDomain
  area_eq : domain.area = d.area
  marked_lower : ENNReal.ofReal d.flux ≤ T.G domain
  universal : ∀ D : ConvexDomain, T.G D ≤
    ENNReal.ofReal (2 * d.stationarity * Real.sqrt d.area * Real.sqrt D.area)

/-- The calibrated reference already has G = Q. -/
theorem reference_attains (T : DirichletTheory) (d : Moments)
    (C : ReferenceCertificate T d) : T.G C.domain = ENNReal.ofReal d.flux := by
  apply le_antisymm _ C.marked_lower
  have h := C.universal C.domain
  rw [C.area_eq] at h
  have hc : 2 * d.stationarity * Real.sqrt d.area * Real.sqrt d.area = d.flux := by
    calc
      _ = 2 * d.stationarity * (Real.sqrt d.area) ^ 2 := by ring
      _ = 2 * d.stationarity * d.area := by rw [Real.sq_sqrt d.area_pos.le]
      _ = d.flux := d.euler.symm
  simpa only [hc] using h

/-- The universal bound, with the exact formula from (1.5). -/
theorem conditional_universal_bound (T : DirichletTheory) (d : Moments)
    (C : ReferenceCertificate T d) (D : ConvexDomain) :
    T.G D ≤ ENNReal.ofReal (d.sharpConstant * Real.sqrt D.area) := by
  simpa only [d.calibration_constant_eq] using C.universal D

/-- Conditional version of the value and attainment assertions in Theorem 1.1.
All analytic input remains visible in `S` and `C`. The conclusion uses the
actual area-one supremum and the actual weak-gradient essential supremum. -/
theorem conditional_exact_value (T : DirichletTheory) (d : Moments)
    (S : ScalingLaw T) (C : ReferenceCertificate T d) :
    T.cStar = ENNReal.ofReal d.sharpConstant ∧
    ∃ D : ConvexDomain, D.area = 1 ∧
      T.G D = ENNReal.ofReal d.sharpConstant := by
  let s : ℝ := (Real.sqrt d.area)⁻¹
  have hroot : 0 < Real.sqrt d.area := Real.sqrt_pos.2 d.area_pos
  have hs : 0 < s := inv_pos.2 hroot
  let D := S.domain s hs C.domain
  have harea : D.area = 1 := by
    change (S.domain s hs C.domain).area = 1
    rw [S.area_eq, C.area_eq]
    dsimp [s]
    rw [inv_pow, Real.sq_sqrt d.area_pos.le]
    exact inv_mul_cancel₀ d.area_pos.ne'
  have hscalar : s * d.flux = d.sharpConstant := by
    dsimp [s]
    rw [mul_comm, ← div_eq_mul_inv]
    exact d.normalized_flux_eq
  have hlower : ENNReal.ofReal d.sharpConstant ≤ T.G D := by
    change ENNReal.ofReal d.sharpConstant ≤ T.G (S.domain s hs C.domain)
    rw [S.gradient_eq, ← hscalar, ENNReal.ofReal_mul hs.le]
    exact mul_le_mul_left' C.marked_lower _
  have hupper : T.G D ≤ ENNReal.ofReal d.sharpConstant := by
    have h := conditional_universal_bound T d C D
    simpa only [harea, Real.sqrt_one, mul_one] using h
  have hattain : T.G D = ENNReal.ofReal d.sharpConstant := le_antisymm hupper hlower
  refine ⟨?_, D, harea, hattain⟩
  apply le_antisymm
  · unfold DirichletTheory.cStar
    refine iSup_le fun E => iSup_le fun hE => ?_
    have h := conditional_universal_bound T d C E
    simpa only [hE, Real.sqrt_one, mul_one] using h
  · unfold DirichletTheory.cStar
    calc
      ENNReal.ofReal d.sharpConstant = T.G D := hattain.symm
      _ ≤ ⨆ (_ : D.area = 1), T.G D := le_iSup (fun _ : D.area = 1 => T.G D) harea
      _ ≤ ⨆ E : ConvexDomain, ⨆ (_ : E.area = 1), T.G E :=
        le_iSup (fun E : ConvexDomain => ⨆ (_ : E.area = 1), T.G E) D

/-- The conditional theorem also establishes finiteness; no use of ENNReal.toReal
can turn an infinite gradient norm into zero. -/
theorem conditional_finite (T : DirichletTheory) (d : Moments)
    (C : ReferenceCertificate T d) (D : ConvexDomain) : T.G D ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (conditional_universal_bound T d C D)

end Torsion
end

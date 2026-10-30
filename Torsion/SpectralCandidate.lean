module

public import Torsion.RestrictedSpectralHilbert
public import Torsion.CauchyConformalGeometry.Convexity
public import Torsion.CauchyImageAreaExact
public import Torsion.ProvedMain
public import Torsion.MarkedFluxLowerBound

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual convex spectral candidate and area-one lower bound

The original weak restricted eigenfunction, with the stated profile shape
and regularity, constructs the actual convex Cauchy image, its exact
Euclidean area and its marked lower bound. The Hilbert equation, convexity,
area identity and weak torsion identification are conclusions of this
pipeline. Selecting the second eigenpair and proving its profile properties
are separate obligations. No universal calibration bound is asserted here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace Torsion.Spectral

/-- The actual convex Cauchy domain and its geometric area are constructed
from the original weak spectral input and stated shape/regularity data. -/
theorem IsRestrictedEigenfunction.cauchy_reference_geometry
    {a : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hconc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x) :
    ∃ D : ConvexDomain, D.carrier = cauchyImage φ ∧
      D.area = a * squareMass φ / 2 ∧ IsMarked D.carrier ∧
      ∀ T : DirichletTheory,
        ENNReal.ofReal (squareMass φ / (2 * mass φ)) ≤ T.G D := by
  obtain ⟨b, hb, _⟩ := hEig.linear_hilbert_equation hφ hα0 hodd
  have ha := hEig.eigenvalue_pos
  have hzero := hEig.1.zero_exterior (hφ.continuous hα0)
  let D := cauchyConvexDomain ha hφ hα0 hα1 hodd hzero hpos hb hconc hd
  have hmarked : IsMarked D.carrier := cauchyImage_isMarked hφ hα0 hα1 hodd hzero hpos
  refine ⟨D, rfl, ?_, hmarked, ?_⟩
  · exact area_cauchyImage_eq_half_squareMass ha.ne' hφ hα0 hα1 hodd hzero hpos hb
  · intro T
    have h := T.torsionFlux_le_G D hmarked
    change ENNReal.ofReal (torsionFlux (cauchyImage φ)) ≤ T.G D at h
    rw [torsionFlux_cauchyImage_eq_squareMass_div_mass
      ha.ne' hφ hα0 hα1 hodd hzero hpos hb] at h
    exact h

/-- The displayed normalized image is an actual area-one convex domain,
and the genuine weak torsion theory has at least the candidate gradient
norm there. This does not use the unproved universal calibration bound. -/
theorem IsRestrictedEigenfunction.normalized_cauchy_candidate
    {a : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hconc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x) :
    ∃ D : ConvexDomain, D.carrier = normalizedImage a φ ∧ D.area = 1 ∧
      ENNReal.ofReal (spectralConstant a φ) ≤ torsionTheory.G D := by
  obtain ⟨b, hb, _⟩ := hEig.linear_hilbert_equation hφ hα0 hodd
  have ha := hEig.eigenvalue_pos
  have hzero := hEig.1.zero_exterior (hφ.continuous hα0)
  let d := momentsOfHolderBoundaryEquation ha hφ hα0 hα1 hodd hzero hpos hb
  let D₀ := cauchyConvexDomain ha hφ hα0 hα1 hodd hzero hpos hb hconc hd
  have harea₀ : D₀.area = d.area :=
    area_cauchyImage_eq_coefficient_mass ha.ne' hφ hα0 hα1 hodd hzero hpos hb
  have hmarked : IsMarked D₀.carrier := cauchyImage_isMarked hφ hα0 hα1 hodd hzero hpos
  have hlower₀ : ENNReal.ofReal d.flux ≤ torsionTheory.G D₀ := by
    have h := torsionTheory.torsionFlux_le_G D₀ hmarked
    change ENNReal.ofReal (torsionFlux (cauchyImage φ)) ≤ torsionTheory.G D₀ at h
    rw [torsionFlux_cauchyImage ha.ne' hφ hα0 hα1 hodd hzero hpos hb] at h
    exact h
  let S := ScalingLaw.proved torsionTheory
  let s : ℝ := (Real.sqrt d.area)⁻¹
  have hs : 0 < s := inv_pos.2 (Real.sqrt_pos.2 d.area_pos)
  let D := S.domain s hs D₀
  have harea : D.area = 1 := by
    change (S.domain s hs D₀).area = 1
    rw [S.area_eq, harea₀]
    dsimp [s]
    rw [inv_pow, Real.sq_sqrt d.area_pos.le]
    exact inv_mul_cancel₀ d.area_pos.ne'
  have hconstant : d.sharpConstant = spectralConstant a φ := rfl
  have hE : d.area = a * squareMass φ / 2 := d.area_eq
  have hscalar : s * d.flux = spectralConstant a φ := by
    dsimp [s]
    rw [mul_comm, ← div_eq_mul_inv, d.normalized_flux_eq, hconstant]
  refine ⟨D, ?_, harea, ?_⟩
  · change (S.domain s hs D₀).carrier = normalizedImage a φ
    rw [S.carrier_eq]
    change (fun z : ℂ => (s : ℂ) * z) '' cauchyImage φ = normalizedImage a φ
    dsimp only [s, normalizedImage, cauchyImage]
    rw [hE]
  · change ENNReal.ofReal (spectralConstant a φ) ≤ torsionTheory.G (S.domain s hs D₀)
    rw [S.gradient_eq, ← hscalar, ENNReal.ofReal_mul hs.le]
    exact mul_le_mul_left' hlower₀ _

/-- Consequently the candidate constant is a genuine lower bound on the
original area-one supremum, without assuming any reference certificate. -/
theorem IsRestrictedEigenfunction.spectralConstant_le_cStar
    {a : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
    (hEig : IsRestrictedEigenfunction a φ)
    (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hodd : Function.Odd φ) (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
    (hconc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x) :
    ENNReal.ofReal (spectralConstant a φ) ≤ torsionTheory.cStar := by
  obtain ⟨D, _, harea, hbound⟩ :=
    hEig.normalized_cauchy_candidate hφ hα0 hα1 hodd hpos hconc hd
  apply hbound.trans
  unfold DirichletTheory.cStar
  exact (le_iSup (fun _ : D.area = 1 => torsionTheory.G D) harea).trans
    (le_iSup (fun E : ConvexDomain => ⨆ (_ : E.area = 1), torsionTheory.G E) D)

end Torsion.Spectral

module

public import Torsion.Main
public import Torsion.SpectralDefinitions

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Explicit connection to the Cauchy-transform domain

`SpectralBridge` lists the still-unproved identification of the concrete
spectral integrals and Cauchy image with the analytic reference certificate.
It is an explicit proof parameter, not an axiom or a constructed instance.
The resulting theorem gives (1.5), including the actual normalized image.
-/

noncomputable section

namespace Torsion

/-- The unresolved bridge from Sections 5--7 to the calibrated reference.
The spectral theorem selecting `a = λ₂` and its eigenfunction is a separate
input; this structure alone does not select the second eigenpair. -/
structure SpectralBridge (T : DirichletTheory) (a : ℝ) (φ : ℝ → ℝ) where
  moments : Moments
  eigenvalue_eq : moments.a = a
  mass_eq : moments.M = Spectral.mass φ
  squareMass_eq : moments.N = Spectral.squareMass φ
  reference : ReferenceCertificate T moments
  image_eq : reference.domain.carrier = Spectral.cauchy φ '' upperHalfPlane

/-- Conditional spectral version of (1.5), with its normalized Cauchy image.
Constructing `B` is the outstanding analytic work, and is not discharged by
this theorem. The essential-supremum and area-one claims are kernel checked. -/
theorem conditional_spectral_exact_value (T : DirichletTheory) (S : ScalingLaw T)
    (a : ℝ) (φ : ℝ → ℝ) (B : SpectralBridge T a φ) :
    T.cStar = ENNReal.ofReal
      (Real.sqrt (Spectral.squareMass φ / (2 * a * (Spectral.mass φ) ^ 2))) ∧
    ∃ D : ConvexDomain,
      D.carrier =
        (fun z : ℂ => ((Real.sqrt (a * Spectral.squareMass φ / 2))⁻¹ : ℂ) * z) ''
          (Spectral.cauchy φ '' upperHalfPlane) ∧
      D.area = 1 ∧
      T.G D = ENNReal.ofReal
        (Real.sqrt (Spectral.squareMass φ / (2 * a * (Spectral.mass φ) ^ 2))) := by
  let d := B.moments
  let C := B.reference
  have hconstant : d.sharpConstant =
      Real.sqrt (Spectral.squareMass φ / (2 * a * (Spectral.mass φ) ^ 2)) := by
    unfold Moments.sharpConstant
    rw [B.eigenvalue_eq, B.mass_eq, B.squareMass_eq]
  have hE : d.area = a * Spectral.squareMass φ / 2 := by
    rw [d.area_eq, B.eigenvalue_eq, B.squareMass_eq]
  refine ⟨?_, ?_⟩
  · rw [← hconstant]
    exact (conditional_exact_value T d S C).1
  let s : ℝ := (Real.sqrt d.area)⁻¹
  have hs : 0 < s := inv_pos.2 (Real.sqrt_pos.2 d.area_pos)
  let D := S.domain s hs C.domain
  have harea : D.area = 1 := by
    change (S.domain s hs C.domain).area = 1
    rw [S.area_eq, C.area_eq]
    dsimp [s]
    rw [inv_pow, Real.sq_sqrt d.area_pos.le]
    exact inv_mul_cancel₀ d.area_pos.ne'
  refine ⟨D, ?_, harea, ?_⟩
  · change (S.domain s hs C.domain).carrier = _
    rw [S.carrier_eq]
    change (fun z : ℂ => (s : ℂ) * z) '' B.reference.domain.carrier = _
    rw [B.image_eq]
    dsimp [s]
    rw [hE]
    simp only [Complex.ofReal_inv]
  · change T.G (S.domain s hs C.domain) = _
    rw [S.gradient_eq, reference_attains T d C, ← ENNReal.ofReal_mul hs.le]
    have hscalar : s * d.flux = d.sharpConstant := by
      dsimp [s]
      rw [mul_comm, ← div_eq_mul_inv]
      exact d.normalized_flux_eq
    rw [hscalar, hconstant]

end Torsion
end

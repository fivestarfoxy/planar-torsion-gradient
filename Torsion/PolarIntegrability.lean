module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Integrability counterpart of mathlib's complex polar integral formula. -/

noncomputable section
open Set MeasureTheory
namespace Torsion

theorem integrable_iff_complex_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) :
    Integrable f ↔ IntegrableOn
      (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p)) polarCoord.target := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  let g : ℝ × ℝ → E := f ∘ Complex.measurableEquivRealProd.symm
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn g
  rw [polarCoord.symm_image_target_eq_source] at h
  simp only [IntegrableOn, Measure.restrict_congr_set polarCoord_source_ae_eq_univ,
    Measure.restrict_univ] at h
  apply h.trans
  apply integrableOn_congr_fun
  · intro p hp
    simp only [det_fderivPolarCoordSymm, abs_of_pos (show 0 < p.1 from hp.1)]
    rfl
  · exact polarCoord.open_target.measurableSet

end Torsion

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Complex differentiation survives conjugation of both source and target. -/
noncomputable section
open Filter
open scoped Topology ComplexConjugate

namespace Torsion.ComplexReflection

theorem hasDerivAt_conj_conj {f : ℂ → ℂ} {f' x : ℂ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun z => conj (f (conj z))) (conj f') (conj x) := by
  rw [hasDerivAt_iff_tendsto] at hf ⊢
  have hc : Tendsto (fun z : ℂ => conj z) (𝓝 (conj x)) (𝓝 x) := by
    simpa using Complex.continuous_conj.tendsto (conj x)
  have ht := hf.comp hc
  convert ht using 1
  ext z
  dsimp only [Function.comp_def]
  have hn : ‖z - conj x‖ = ‖conj z - x‖ := by
    rw [← Complex.norm_conj (z - conj x)]
    simp
  rw [hn]
  congr 1
  rw [← Complex.norm_conj (f (conj z) - f x - (conj z - x) • f')]
  simp [smul_eq_mul]

end Torsion.ComplexReflection

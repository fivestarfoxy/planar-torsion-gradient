import Torsion.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Scalar closure of the concrete zero-boundary Sobolev graph

The approximation witnesses are scaled directly, both for the values and the
weak gradients. No closure property is postulated.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- Real scalar multiplication commutes with the classical gradient of a
smooth approximating function. -/
theorem gradient_real_const_smul {f : Plane → ℝ} (hf : Differentiable ℝ f)
    (c : ℝ) (x : Plane) :
    gradient (fun y => c • f y) x = c • gradient f x := by
  unfold gradient
  rw [fderiv_const_smul (hf x) c]
  exact map_smul ((InnerProductSpace.toDual ℝ Plane).symm) c (fderiv ℝ f x)

/-- Multiplication by a real constant preserves the smooth compact test core. -/
theorem IsTest.const_smul {D : Set Plane} {f : Plane → ℝ}
    (hf : IsTest D f) (c : ℝ) : IsTest D (fun x => c • f x) := by
  refine ⟨hf.1.const_smul c, ?_, ?_⟩
  · exact HasCompactSupport.smul_left (f := fun _ : Plane => c) hf.2.1
  · exact (tsupport_smul_subset_right (fun _ : Plane => c) f).trans hf.2.2

/-- The negative of a test function remains a test function. -/
theorem IsTest.neg {D : Set Plane} {f : Plane → ℝ}
    (hf : IsTest D f) : IsTest D (fun x => -f x) := by
  simpa using hf.const_smul (-1 : ℝ)

/-- The zero function belongs to the test core of every set. -/
theorem isTest_zero (D : Set Plane) : IsTest D (fun _ => 0) := by
  have hz : tsupport (fun _ : Plane => (0 : ℝ)) = ∅ :=
    tsupport_eq_empty_iff.mpr rfl
  refine ⟨contDiff_const, ?_, ?_⟩
  · change IsCompact (tsupport (fun _ : Plane => (0 : ℝ)))
    rw [hz]
    exact isCompact_empty
  · rw [hz]
    exact empty_subset D

/-- Zero value and zero gradient are in the defining Sobolev graph. -/
theorem memH10_zero (D : Set Plane) : MemH10 D (fun _ => 0) (fun _ => 0) := by
  refine ⟨MemLp.zero', MemLp.zero', (fun _ _ => 0), (fun _ => isTest_zero D), ?_, ?_⟩
  · simp
  · simp [gradient_const]

/-- The zero-boundary Sobolev graph is closed under real scalar multiplication,
proved by scaling its simultaneous value/gradient approximations. -/
theorem MemH10.const_smul {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) (c : ℝ) :
    MemH10 D (fun x => c • u x) (fun x => c • g x) := by
  obtain ⟨hmu, hmg, f, hf, hval, hgrad⟩ := hu
  refine ⟨hmu.const_smul c, hmg.const_smul c,
    (fun n x => c • f n x), (fun n => (hf n).const_smul c), ?_, ?_⟩
  · have heq (n : ℕ) :
        (fun x => c • f n x - c • u x) = c • (fun x => f n x - u x) := by
      funext x
      simp only [Pi.smul_apply, smul_sub]
    simp_rw [heq, eLpNorm_const_smul]
    simpa using ENNReal.Tendsto.const_mul hval (Or.inr (enorm_ne_top (x := c)))
  · have heq (n : ℕ) :
        (fun x => gradient (fun y => c • f n y) x - c • g x) =
          c • (fun x => gradient (f n) x - g x) := by
      funext x
      rw [gradient_real_const_smul ((hf n).1.differentiable (by simp)) c x]
      simp only [Pi.smul_apply, smul_sub]
    simp_rw [heq, eLpNorm_const_smul]
    simpa using ENNReal.Tendsto.const_mul hgrad (Or.inr (enorm_ne_top (x := c)))

/-- Negating a zero-boundary Sobolev value negates its weak gradient. -/
theorem MemH10.neg {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) : MemH10 D (fun x => -u x) (fun x => -g x) := by
  simpa using hu.const_smul (-1 : ℝ)

end Torsion

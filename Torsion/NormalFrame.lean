module

public import Torsion.TorsionIsometry
public import Torsion.TorsionTranslation
public import Mathlib.Analysis.Complex.Isometry

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Physical orthogonal coordinates at a supporting boundary point -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Torsion

/-- The oriented orthogonal frame whose inward vertical vector is `n`. -/
def normalFrame (n : Plane) (hn : ‖n‖ = 1) : Plane ≃ₗᵢ[ℝ] Plane :=
  rotation ⟨-Complex.I * n, by
    simp [Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right,
      norm_mul, hn]⟩

@[simp] theorem normalFrame_I (n : Plane) (hn : ‖n‖ = 1) :
    normalFrame n hn Complex.I = n := by
  change (-Complex.I * n) * Complex.I = n
  calc
    _ = -(Complex.I * Complex.I) * n := by ring
    _ = n := by rw [Complex.I_mul_I]; ring

/-- The normal coordinate is the actual Euclidean inner product. -/
theorem normalFrame_symm_im (n : Plane) (hn : ‖n‖ = 1) (z : Plane) :
    ((normalFrame n hn).symm z).im = inner (𝕜 := ℝ) n z := by
  have h := (normalFrame n hn).inner_map_map Complex.I ((normalFrame n hn).symm z)
  rw [normalFrame_I, LinearIsometryEquiv.apply_symm_apply] at h
  simpa [Complex.inner, Complex.mul_re] using h.symm

namespace ConvexDomain

/-- Translate the chosen point to zero and align its actual unit inward
normal with the positive imaginary axis. -/
def inNormalFrame (D : ConvexDomain) (p n : Plane) (hn : ‖n‖ = 1) : ConvexDomain :=
  (D.translate (-p)).isometryPreimage (normalFrame n hn)

@[simp] theorem mem_inNormalFrame (D : ConvexDomain) (p n z : Plane) (hn : ‖n‖ = 1) :
    z ∈ (D.inNormalFrame p n hn).carrier ↔ normalFrame n hn z + p ∈ D.carrier := by
  simp only [inNormalFrame, mem_isometryPreimage, mem_translate, sub_neg_eq_add]

@[simp] theorem inNormalFrame_area (D : ConvexDomain) (p n : Plane) (hn : ‖n‖ = 1) :
    (D.inNormalFrame p n hn).area = D.area := by
  simp only [inNormalFrame, isometryPreimage_area, translate_area]

theorem inNormalFrame_subset_upper (D : ConvexDomain) (p n : Plane) (hn : ‖n‖ = 1)
    (hpos : ∀ z ∈ D.carrier, 0 < inner (𝕜 := ℝ) n (z - p)) :
    (D.inNormalFrame p n hn).carrier ⊆ upperHalfPlane := by
  intro z hz
  have h := hpos _ ((mem_inNormalFrame D p n z hn).mp hz)
  rw [add_sub_cancel_right, ← normalFrame_symm_im n hn,
    LinearIsometryEquiv.symm_apply_apply] at h
  exact h

theorem zero_mem_closure_inNormalFrame (D : ConvexDomain) (p n : Plane) (hn : ‖n‖ = 1)
    (hp : p ∈ closure D.carrier) :
    (0 : Plane) ∈ closure (D.inNormalFrame p n hn).carrier := by
  let e : Plane ≃ₜ Plane := (normalFrame n hn).toHomeomorph.trans (Homeomorph.addRight p)
  have hdom : (D.inNormalFrame p n hn).carrier = e ⁻¹' D.carrier := by
    ext z
    exact mem_inNormalFrame D p n z hn
  rw [hdom, ← e.preimage_closure]
  change normalFrame n hn 0 + p ∈ closure D.carrier
  simpa only [map_zero, zero_add] using hp

end ConvexDomain

/-- The actual weak equation in boundary normal coordinates, including its
physical orthogonal weak gradient. -/
theorem IsWeakTorsion.inNormalFrame {D : ConvexDomain}
    {u : Plane → ℝ} {g : Plane → Plane} (hu : IsWeakTorsion D.carrier u g)
    (p n : Plane) (hn : ‖n‖ = 1) :
    IsWeakTorsion (D.inNormalFrame p n hn).carrier
      (fun z => u (normalFrame n hn z + p))
      (isometryGradient (normalFrame n hn) (Torsion.translatedValue (-p) g)) := by
  have h := (hu.translatedValue D.isOpen.measurableSet (-p)).isometry_comp
    (D.translate (-p)).isOpen.measurableSet (normalFrame n hn)
  simpa only [ConvexDomain.inNormalFrame, ConvexDomain.isometryPreimage,
    ConvexDomain.translate, Torsion.translatedValue, sub_neg_eq_add] using h

@[simp] theorem DirichletTheory.G_inNormalFrame (T : DirichletTheory)
    (D : ConvexDomain) (p n : Plane) (hn : ‖n‖ = 1) :
    T.G (D.inNormalFrame p n hn) = T.G D := by
  simp only [ConvexDomain.inNormalFrame, G_isometryPreimage, G_translate]

end Torsion

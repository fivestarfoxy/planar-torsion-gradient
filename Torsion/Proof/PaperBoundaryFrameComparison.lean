module

public import Torsion.Proof.PaperBoundaryFrame
public import Torsion.Proof.PaperBoundaryLimit
public import Torsion.Proof.PaperRectangleComparison

@[expose] public section

/-! # The rectangle comparison along genuine maximizing boundary samples -/

noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal ContDiff

namespace Torsion.MaximizingNormalSequence

/-- Apply the proved rectangle estimate to the original weak solution at
every sampled supporting frame, with the same sharp Lipschitz constant. -/
theorem rectangleComparison {T : DirichletTheory} {D : ConvexDomain}
    (s : MaximizingNormalSequence T D) : s.RectangleComparison := by
  intro j R δ η hR hδ hη hηL hroof htR
  let p := s.points j
  let n := s.normals j
  let e := normalFrame n (s.sample_unit j)
  let E := D.inNormalFrame p n (s.sample_unit j)
  let U (z : Plane) := s.value (e z + p)
  have hweak := s.weak.inNormalFrame p n (s.sample_unit j)
  have hLip : LipschitzWith (T.G D).toNNReal U :=
    lipschitzWith_inNormalFrame s.lipschitz p n (s.sample_unit j)
  have hz (z : Plane) (hzE : z ∉ E.carrier) : U z = 0 :=
    s.zero_off _ (fun hx => hzE ((D.mem_inNormalFrame p n z (s.sample_unit j)).mpr hx))
  have hhalf := D.inNormalFrame_subset_upper p n (s.sample_unit j) (s.sample_support j)
  obtain ⟨hs, hg⟩ := hweak.continuous_zero_extension_interior_data hLip.continuous hz
  have hr (z : Plane) (hzre : |z.re| ≤ δ * R) (hzim : z.im = R) :
      U z ≤ ((T.G D).toReal - η) * R := by
    change s.value (normalFrame n (s.sample_unit j) z + p) ≤ _
    rw [normalFrame_coordinates, hzim]
    simpa only [p, n, add_comm, add_left_comm, add_assoc] using hroof z.re hzre
  let t := s.depths j
  have hcoord : e ((t : Plane) * Complex.I) + p = p + t • n := by
    rw [← Complex.real_smul, map_smul, show e Complex.I = n from normalFrame_I n (s.sample_unit j),
      add_comm]
  have hin : (t : Plane) * Complex.I ∈ E.carrier := by
    apply (D.mem_inNormalFrame p n _ (s.sample_unit j)).mpr
    change e ((t : Plane) * Complex.I) + p ∈ D.carrier
    rw [hcoord]
    exact s.sample_inside j
  have hbound := supporting_rectangle_quotient_le E hweak hhalf hs hg hz
    (T.G D).toNNReal hLip hR hδ hη hηL hr (s.depth_pos j) htR hin
  change s.value (e ((t : Plane) * Complex.I) + p) / t ≤ _ at hbound
  rwa [hcoord] at hbound

end Torsion.MaximizingNormalSequence

module

public import Torsion.Proof.PaperBrownianLifetime
public import Torsion.Proof.PaperBrownianExhaustion
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

@[expose] public section

/-! # The first exit from an open set is an integrable random variable -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace Torsion.Brownian
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private theorem continuousPath_exit_measurable {D : Set Plane} (hD : IsOpen D) :
    Measurable (pathExitTime D (fun (t : ℝ≥0) (f : C(ℝ≥0, Plane)) => f t)) := by
  apply measurable_of_Ioi
  intro q
  induction q using ENNReal.recTopCoe with
  | top => simp
  | coe t =>
    convert (ContinuousMap.isOpen_setOfPred_mapsTo (isCompact_Icc (a := 0) (b := t)) hD).measurableSet using 1
    ext f
    change (t : ℝ≥0∞) < pathExitTime D (fun s (g : C(ℝ≥0, Plane)) => g s) f ↔ MapsTo f (Icc 0 t) D
    constructor
    · intro hs u hu
      exact not_not.mp (notMem_of_lt_hittingAfter ((ENNReal.coe_le_coe.mpr hu.2).trans_lt hs) zero_le)
    · intro hm
      by_contra! he
      have hfin := ne_top_of_le_ne_top ENNReal.coe_ne_top he
      have hhit := pathExitTime_mem_compl hD f.continuous hfin
      exact hhit (hm ⟨zero_le, by exact_mod_cast (ENNReal.coe_toNNReal hfin ▸ he)⟩)

/-- Sample paths are almost surely continuous. Their open-domain exit is an
a.e. measurable real extended lifetime on the original probability space. -/
theorem IsPlanarBrownian.aemeasurable_exitTime {B : ℝ≥0 → Ω → Plane} (hB : IsPlanarBrownian B P)
    {D : Set Plane} (hD : IsOpen D) (x : Plane) : AEMeasurable (exitTime D x B) P := by
  classical
  let path : Ω → C(ℝ≥0, Plane) := fun ω =>
    if h : Continuous (fun t => x + B t ω) then ⟨_,h⟩ else 0
  have hc := hB.continuous_paths x
  have hev (t : ℝ≥0) : AEMeasurable (fun ω => path ω t) P := by
    have hb : AEMeasurable (B t) P :=
      Complex.equivRealProdCLM.symm.continuous.measurable.comp_aemeasurable
        ((hB.re.aemeasurable t).prodMk (hB.im.aemeasurable t))
    apply ((aemeasurable_const (b := x)).add hb).congr
    filter_upwards [hc] with ω hω
    simp [path, hω]
  have hp : NullMeasurable path P := by
    change @Measurable (NullMeasurableSpace Ω P) C(ℝ≥0, Plane) _ _ path
    exact ContinuousMap.measurable_iff_eval.mpr fun t => (hev t).nullMeasurable
  let T := pathExitTime D (fun (t : ℝ≥0) (f : C(ℝ≥0, Plane)) => f t)
  have ht : NullMeasurable (T ∘ path) P := fun _ hs => hp ((continuousPath_exit_measurable hD) hs)
  apply ht.aemeasurable.congr
  filter_upwards [hc] with ω hω
  change T (path ω) = exitTime D x B ω
  rw [show path ω = ⟨_, hω⟩ from dite_eq_left hω]
  rfl

/-- The Brownian sample exits every bounded open planar set almost surely. -/
theorem IsPlanarBrownian.ae_exitTime_lt_top {B : ℝ≥0 → Ω → Plane} (hB : IsPlanarBrownian B P)
    {D : Set Plane} (ho : IsOpen D) (hD : Bornology.IsBounded D) (x : Plane) :
    ∀ᵐ ω ∂P, exitTime D x B ω < ⊤ :=
  ae_lt_top' (hB.aemeasurable_exitTime ho x) (hB.lintegral_exitTime_lt_top hD x).ne

/-- The real-valued first exit time has a finite expectation. -/
theorem IsPlanarBrownian.integrable_exitTime {B : ℝ≥0 → Ω → Plane} (hB : IsPlanarBrownian B P)
    {D : Set Plane} (ho : IsOpen D) (hD : Bornology.IsBounded D) (x : Plane) :
    Integrable (fun ω => (exitTime D x B ω).toReal) P :=
  integrable_toReal_of_lintegral_ne_top (hB.aemeasurable_exitTime ho x) (hB.lintegral_exitTime_lt_top hD x).ne

end Torsion.Brownian

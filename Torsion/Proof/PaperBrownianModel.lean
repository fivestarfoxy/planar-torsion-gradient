module

public import Torsion.Definitions
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

/-! # Standard planar Brownian motion and the first exit time -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal
namespace Torsion.Brownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The two real coordinates are standard Brownian motions and their entire
coordinate processes are independent. -/
structure IsPlanarBrownian (B : ℝ≥0 → Ω → Plane) (P : Measure Ω) : Prop where
  re : IsBrownianReal (fun t ω => (B t ω).re) P
  im : IsBrownianReal (fun t ω => (B t ω).im) P
  independent : IndepFun (fun ω t => (B t ω).re) (fun ω t => (B t ω).im) P

/-- The first continuous time at which Brownian motion started at x is outside D. -/
def exitTime (D : Set Plane) (x : Plane) (B : ℝ≥0 → Ω → Plane) : Ω → ℝ≥0∞ :=
  hittingAfter (fun t ω => x + B t ω) Dᶜ 0

/-- Almost surely the translated process starts at the prescribed point. -/
theorem IsPlanarBrownian.starts_at {B : ℝ≥0 → Ω → Plane} (hB : IsPlanarBrownian B P) (x : Plane) :
    ∀ᵐ ω ∂P, x + B 0 ω = x := by
  filter_upwards [hB.re.eval_zero_ae_eq_zero, hB.im.eval_zero_ae_eq_zero] with ω hr hi
  have h0 : B 0 ω = 0 := Complex.ext hr hi
  rw [h0, add_zero]

/-- Almost every physical path is continuous. -/
theorem IsPlanarBrownian.continuous_paths {B : ℝ≥0 → Ω → Plane} (hB : IsPlanarBrownian B P) (x : Plane) :
    ∀ᵐ ω ∂P, Continuous (fun t => x + B t ω) := by
  filter_upwards [hB.re.cont, hB.im.cont] with ω hr hi
  exact continuous_const.add (Complex.equivRealProdCLM.symm.continuous.comp (hr.prodMk hi))

omit [MeasurableSpace Ω] in
/-- Every time strictly before first exit lies in the original domain. -/
theorem mem_of_lt_exitTime {D : Set Plane} {x : Plane} {B : ℝ≥0 → Ω → Plane} {ω : Ω} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < exitTime D x B ω) : x + B t ω ∈ D :=
  not_not.mp (notMem_of_lt_hittingAfter ht zero_le)

end Torsion.Brownian

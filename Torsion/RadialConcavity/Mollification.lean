module

public import Torsion.RadialConcavity
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The continuous case of homogeneous supermodular concavity

Log-coordinate mollification preserves degree-one homogeneity and the lattice
inequality. This file constructs that mollification with normalized smooth bump
kernels, invokes the proved smooth theorem, and passes to the limit.
-/

noncomputable section
namespace Torsion.RadialConcavity

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Convolution

variable {ι : Type*} [Fintype ι]

private def dilate (s x : Vec ι) : Vec ι := fun i => Real.exp (-s i) * x i

omit [Fintype ι] in
private theorem dilate_positive (s : Vec ι) {x : Vec ι} (hx : x ∈ positiveOrthant) :
    dilate s x ∈ positiveOrthant :=
  fun i => mul_pos (Real.exp_pos _) (hx i)

omit [Fintype ι] in
private theorem continuous_dilate (x : Vec ι) : Continuous (fun s => dilate s x) := by
  apply continuous_pi
  intro i
  exact (Real.continuous_exp.comp (continuous_apply i).neg).mul continuous_const

omit [Fintype ι] in
private theorem dilate_smul (s x : Vec ι) (t : ℝ) : dilate s (t • x) = t • dilate s x := by
  ext i
  simp [dilate, smul_eq_mul]
  ring

omit [Fintype ι] in
private theorem dilate_sup (s x y : Vec ι) : dilate s (x ⊔ y) = dilate s x ⊔ dilate s y := by
  ext i
  exact mul_max_of_nonneg (x i) (y i) (Real.exp_pos _).le

omit [Fintype ι] in
private theorem dilate_inf (s x y : Vec ι) : dilate s (x ⊓ y) = dilate s x ⊓ dilate s y := by
  ext i
  exact mul_min_of_nonneg (x i) (y i) (Real.exp_pos _).le

private def expLift (F : Vec ι → ℝ) (z : Vec ι) : ℝ := F (fun i => Real.exp (z i))
private def logVec (x : Vec ι) : Vec ι := fun i => Real.log (x i)

omit [Fintype ι] in
private theorem continuous_expLift {F : Vec ι → ℝ} (hF : ContinuousOn F positiveOrthant) :
    Continuous (expLift F) := by
  apply hF.comp_continuous
  · apply continuous_pi
    intro i
    exact Real.continuous_exp.comp (continuous_apply i)
  · intro z i
    exact Real.exp_pos _

private theorem contDiffOn_logVec : ContDiffOn ℝ 2 (logVec : Vec ι → Vec ι) positiveOrthant := by
  apply contDiffOn_pi.mpr
  intro i
  apply Real.contDiffOn_log.comp (contDiff_apply ℝ ℝ i).contDiffOn
  intro x hx
  exact (hx i).ne'

private def mollify (φ : ContDiffBump (0 : Vec ι)) (F : Vec ι → ℝ) (x : Vec ι) : ℝ :=
  ∫ s, φ.normed volume s * F (dilate s x)

private theorem mollify_eq_convolution (φ : ContDiffBump (0 : Vec ι)) (F : Vec ι → ℝ)
    {x : Vec ι} (hx : x ∈ positiveOrthant) :
    mollify φ F x = (φ.normed volume ⋆[lsmul ℝ ℝ] expLift F) (logVec x) := by
  rw [mollify, convolution_def]
  apply integral_congr_ae
  filter_upwards with s
  congr 1
  apply congrArg F
  ext i
  simp [dilate, expLift, logVec, Real.exp_sub, Real.exp_log (hx i), Real.exp_neg]
  ring

private theorem mollify_integrable (φ : ContDiffBump (0 : Vec ι)) {F : Vec ι → ℝ}
    (hF : ContinuousOn F positiveOrthant) {x : Vec ι} (hx : x ∈ positiveOrthant) :
    Integrable (fun s => φ.normed volume s * F (dilate s x)) := by
  have hc : Continuous (fun s => F (dilate s x)) :=
    hF.comp_continuous (continuous_dilate x) (fun s => dilate_positive s hx)
  exact (φ.continuous_normed.mul hc).integrable_of_hasCompactSupport
    φ.hasCompactSupport_normed.mul_right

private theorem homogeneous_mollify (φ : ContDiffBump (0 : Vec ι)) {F : Vec ι → ℝ}
    (hhom : Homogeneous F) : Homogeneous (mollify φ F) := by
  intro x hx t ht
  unfold mollify
  calc
    _ = ∫ s, t * (φ.normed volume s * F (dilate s x)) := by
      apply integral_congr_ae
      filter_upwards with s
      rw [dilate_smul, hhom _ (dilate_positive s hx) t ht]
      ring
    _ = _ := integral_const_mul _ _

private theorem supermodular_mollify (φ : ContDiffBump (0 : Vec ι)) {F : Vec ι → ℝ}
    (hF : ContinuousOn F positiveOrthant) (hsuper : Supermodular F) :
    Supermodular (mollify φ F) := by
  intro x hx y hy
  have hsup : x ⊔ y ∈ positiveOrthant := fun i => lt_sup_of_lt_left (hx i)
  have hinf : x ⊓ y ∈ positiveOrthant := fun i => lt_min (hx i) (hy i)
  have hix := mollify_integrable φ hF hx
  have hiy := mollify_integrable φ hF hy
  have hisup := mollify_integrable φ hF hsup
  have hiinf := mollify_integrable φ hF hinf
  unfold mollify
  rw [← integral_add hix hiy, ← integral_add hisup hiinf]
  apply integral_mono (hix.add hiy) (hisup.add hiinf)
  intro s
  have hs := mul_le_mul_of_nonneg_left
    (hsuper _ (dilate_positive s hx) _ (dilate_positive s hy)) (φ.nonneg_normed (μ := volume) s)
  simpa [dilate_sup, dilate_inf, mul_add] using hs

private theorem contDiffOn_mollify (φ : ContDiffBump (0 : Vec ι)) {F : Vec ι → ℝ}
    (hF : ContinuousOn F positiveOrthant) :
    ContDiffOn ℝ 2 (mollify φ F) positiveOrthant := by
  have hc : ContDiff ℝ 2 (φ.normed volume ⋆[lsmul ℝ ℝ] expLift F) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      (continuous_expLift hF).locallyIntegrable
  apply (hc.comp_contDiffOn contDiffOn_logVec).congr
  intro x hx
  exact mollify_eq_convolution φ F hx

private def shrinkingBump (n : ℕ) : ContDiffBump (0 : Vec ι) :=
  ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1),
    half_pos (by positivity), half_lt_self (by positivity)⟩

private theorem mollify_tendsto {F : Vec ι → ℝ} (hF : ContinuousOn F positiveOrthant)
    {x : Vec ι} (hx : x ∈ positiveOrthant) :
    Tendsto (fun n : ℕ => mollify (shrinkingBump n) F x) atTop (𝓝 (F x)) := by
  have hrad : Tendsto (fun n : ℕ => (shrinkingBump (ι := ι) n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hc := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) hrad (continuous_expLift hF) (logVec x)
  have hxlog : expLift F (logVec x) = F x := by
    change F (fun i => Real.exp (Real.log (x i))) = F x
    apply congrArg F
    ext i
    exact Real.exp_log (hx i)
  simpa only [← mollify_eq_convolution _ _ hx, hxlog] using hc

/-- Lemma 3.4 in its full continuous form. A continuous, degree-one positively
homogeneous, supermodular function on a finite-dimensional positive orthant
is concave. The proof constructs smooth log-coordinate convolutions and
passes their concavity inequalities to the limit. -/
theorem concave_of_continuous_homogeneous_supermodular {F : Vec ι → ℝ}
    (hF : ContinuousOn F positiveOrthant)
    (hhom : Homogeneous F) (hsuper : Supermodular F) :
    ConcaveOn ℝ positiveOrthant F := by
  classical
  refine ⟨convex_positiveOrthant, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a • x + b • y ∈ positiveOrthant :=
    convex_positiveOrthant hx hy ha hb hab
  have hconcave : ∀ n : ℕ, ConcaveOn ℝ positiveOrthant (mollify (shrinkingBump n) F) := by
    intro n
    apply concave_of_contDiff_homogeneous_supermodular
      (contDiffOn_mollify _ hF) (homogeneous_mollify _ hhom) (supermodular_mollify _ hF hsuper)
  have hleft := ((mollify_tendsto hF hx).const_smul a).add
    ((mollify_tendsto hF hy).const_smul b)
  exact le_of_tendsto_of_tendsto hleft (mollify_tendsto hF hz)
    (Eventually.of_forall fun n => (hconcave n).2 hx hy ha hb hab)

end Torsion.RadialConcavity

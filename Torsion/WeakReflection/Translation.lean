module

public import Torsion.WeakGradient
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Translation of the concrete H¹₀ graph and strong L² continuity. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

def translatedValue {E : Type*} (a : Plane) (u : Plane → E) (z : Plane) : E := u (z - a)

theorem measurePreserving_sub_const (a : Plane) :
    MeasurePreserving (fun z : Plane => z - a) volume volume := by
  simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-a)

theorem eLpNorm_translatedValue {E : Type*} [NormedAddCommGroup E]
    (a : Plane) (u : Plane → E) (p : ℝ≥0∞) :
    eLpNorm (translatedValue a u) p volume = eLpNorm u p volume := by
  have he := (Homeomorph.subRight a).toMeasurableEquiv.measurableEmbedding
  change eLpNorm (u ∘ (Homeomorph.subRight a).toMeasurableEquiv) p volume = _
  rw [← he.eLpNorm_map_measure]
  change eLpNorm u p (Measure.map (fun z : Plane => z - a) volume) = _
  rw [(measurePreserving_sub_const a).map_eq]

theorem memLp_translatedValue {E : Type*} [NormedAddCommGroup E]
    {u : Plane → E} {p : ℝ≥0∞} (hu : MemLp u p volume) (a : Plane) :
    MemLp (translatedValue a u) p volume :=
  hu.comp_measurePreserving (measurePreserving_sub_const a)

theorem gradient_translatedValue {u : Plane → ℝ} {a z : Plane}
    (hu : DifferentiableAt ℝ u (z - a)) :
    gradient (translatedValue a u) z = translatedValue a (gradient u) z := by
  have hi : HasFDerivAt (fun y : Plane => y - a) (ContinuousLinearMap.id ℝ Plane) z :=
    (hasFDerivAt_id z).sub_const a
  have hd := hu.hasGradientAt.hasFDerivAt.comp z hi
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hd using 1
  · funext x
    rfl
  · simp only [translatedValue, ContinuousLinearMap.comp_id]

theorem IsTest.translatedValue {D : Set Plane} {f : Plane → ℝ}
    (hf : IsTest D f) (a : Plane) :
    IsTest ((fun z : Plane => z - a) ⁻¹' D) (Torsion.translatedValue a f) := by
  refine ⟨hf.1.comp (contDiff_id.sub contDiff_const),
    hf.2.1.comp_homeomorph (Homeomorph.subRight a), ?_⟩
  have hsupp : tsupport (Torsion.translatedValue a f) ⊆
      (fun z : Plane => z - a) ⁻¹' tsupport f := by
    apply closure_minimal
    · intro z hz
      exact subset_tsupport f hz
    · exact (isClosed_tsupport f).preimage (continuous_id.sub continuous_const)
  exact hsupp.trans (preimage_mono hf.2.2)

theorem MemH10.translatedValue {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) (a : Plane) :
    MemH10 ((fun z : Plane => z - a) ⁻¹' D)
      (Torsion.translatedValue a u) (Torsion.translatedValue a g) := by
  obtain ⟨hmu, hmg, f, hf, hv, hg⟩ := hu
  refine ⟨memLp_translatedValue hmu a, memLp_translatedValue hmg a,
    fun n => Torsion.translatedValue a (f n), fun n => (hf n).translatedValue a, ?_, ?_⟩
  · convert hv using 1
    funext n
    exact eLpNorm_translatedValue a (fun x => f n x - u x) 2
  · have heq (n : ℕ) :
        (fun x => gradient (Torsion.translatedValue a (f n)) x - Torsion.translatedValue a g x) =
          Torsion.translatedValue a (fun x => gradient (f n) x - g x) := by
      funext x
      rw [gradient_translatedValue ((hf n).1.differentiable (by simp) _)]
      rfl
    simpa only [heq, eLpNorm_translatedValue] using hg

/-- Translations tending to zero converge strongly in the actual L² norm. -/
theorem tendsto_eLpNorm_translatedValue_sub {E : Type*} [NormedAddCommGroup E]
    {u : Plane → E} (hu : MemLp u 2 volume) {a : ℕ → Plane}
    (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => translatedValue (a n) u x - u x) 2 volume)
      atTop (𝓝 0) := by
  let maps : Plane → C(Plane, Plane) := fun b =>
    ⟨fun x => x - b, continuous_id.sub continuous_const⟩
  have hmaps : Continuous maps := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_snd.sub continuous_fst
  have hlim : Tendsto (fun n => Lp.compMeasurePreserving (maps (a n))
      (measurePreserving_sub_const (a n)) (hu.toLp u)) atTop
      (𝓝 (Lp.compMeasurePreserving (maps 0) (measurePreserving_sub_const 0)
        (hu.toLp u))) :=
    tendsto_const_nhds.compMeasurePreservingLp ((hmaps.tendsto 0).comp ha)
      (fun n => measurePreserving_sub_const (a n))
      (measurePreserving_sub_const 0) (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))
  have hzero : Lp.compMeasurePreserving (maps 0)
      (measurePreserving_sub_const 0) (hu.toLp u) = hu.toLp u := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (hu.toLp u)
      (measurePreserving_sub_const 0)] with x hx
    simpa [maps] using hx
  rw [hzero] at hlim
  have heq (n : ℕ) : Lp.compMeasurePreserving (maps (a n))
      (measurePreserving_sub_const (a n)) (hu.toLp u) =
      (memLp_translatedValue hu (a n)).toLp (translatedValue (a n) u) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (hu.toLp u)
        (measurePreserving_sub_const (a n)),
      (measurePreserving_sub_const (a n)).quasiMeasurePreserving.ae hu.coeFn_toLp,
      (memLp_translatedValue hu (a n)).coeFn_toLp] with x hx hy hz
    exact hx.trans (hy.trans hz.symm)
  simpa only [heq, Lp.edist_toLp_toLp, Pi.sub_def] using
    (tendsto_iff_edist_tendsto_0.mp hlim)

end Torsion

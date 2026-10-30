module

public import Torsion.SobolevCore

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Zero extension inherited by the Sobolev graph closure

Both coordinates vanish almost everywhere off the domain. This is proved from
the actual simultaneous approximations. No regularity or measurability of the
domain is required: each approximant vanishes off its own closed support, and
restriction to the domain complement is dominated by restriction to that
measurable support complement.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion

/-- A compact test function vanishes almost everywhere off its domain. -/
theorem IsTest.value_ae_zero_off {D : Set Plane} {f : Plane → ℝ}
    (hf : IsTest D f) : f =ᵐ[volume.restrict Dᶜ] 0 := by
  apply ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.mpr hf.2.2)
  apply ae_restrict_of_forall_mem (isClosed_closure.measurableSet.compl)
  intro x hx
  change f x = 0
  by_contra hne
  exact hx (subset_closure hne)

/-- The gradient of a compact test function vanishes almost everywhere off its domain. -/
theorem IsTest.gradient_ae_zero_off {D : Set Plane} {f : Plane → ℝ}
    (hf : IsTest D f) : gradient f =ᵐ[volume.restrict Dᶜ] 0 := by
  apply ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.mpr hf.2.2)
  apply ae_restrict_of_forall_mem (isClosed_closure.measurableSet.compl)
  intro x hx
  exact gradient_eq_zero_of_not_mem_tsupport hx

private theorem ae_zero_off_of_eLpNorm_approximation
    {E : Type*} [NormedAddCommGroup E] {D : Set Plane} {u : Plane → E}
    (hu : MemLp u 2 volume) (f : ℕ → Plane → E)
    (hf : ∀ n, f n =ᵐ[volume.restrict Dᶜ] 0)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 volume)
      atTop (𝓝 0)) :
    u =ᵐ[volume.restrict Dᶜ] 0 := by
  have hrestrict : Tendsto
      (fun n => eLpNorm (fun x => f n x - u x) 2 (volume.restrict Dᶜ)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    · intro n
      exact zero_le
    · intro n
      exact eLpNorm_restrict_le _ _ _ _
  have heq (n : ℕ) :
      eLpNorm (fun x => f n x - u x) 2 (volume.restrict Dᶜ) =
        eLpNorm u 2 (volume.restrict Dᶜ) := by
    calc
      _ = eLpNorm (fun x => -u x) 2 (volume.restrict Dᶜ) := by
        apply eLpNorm_congr_ae
        filter_upwards [hf n] with x hx
        simp only [Pi.zero_apply] at hx
        simp only [hx, zero_sub]
      _ = _ := eLpNorm_neg u 2 (volume.restrict Dᶜ)
  have hconst : Tendsto (fun _ : ℕ => eLpNorm u 2 (volume.restrict Dᶜ))
      atTop (𝓝 0) := by simpa only [heq] using hrestrict
  have hzero : eLpNorm u 2 (volume.restrict Dᶜ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  exact (eLpNorm_eq_zero_iff (by norm_num)).mp hzero

/-- The value coordinate of a zero-boundary Sobolev function is zero almost
 everywhere on the complement, inherited from its compact approximants. -/
theorem MemH10.value_ae_zero_off {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) : u =ᵐ[volume.restrict Dᶜ] 0 := by
  obtain ⟨hmu, hmg, f, hf, hval, hgrad⟩ := hu
  exact ae_zero_off_of_eLpNorm_approximation hmu f
    (fun n => (hf n).value_ae_zero_off) hval

/-- The weak gradient coordinate is also zero almost everywhere off the domain. -/
theorem MemH10.gradient_ae_zero_off {D : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : MemH10 D u g) : g =ᵐ[volume.restrict Dᶜ] 0 := by
  obtain ⟨hmu, hmg, f, hf, hval, hgrad⟩ := hu
  exact ae_zero_off_of_eLpNorm_approximation hmg (fun n => gradient (f n))
    (fun n => (hf n).gradient_ae_zero_off) hgrad

end Torsion

import Torsion.WeakHarmonicRegularity

/-! # Commuting compact smoothing kernels against an actual L² field -/
noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ENNReal ContDiff Convolution

namespace Torsion.WeakHarmonicRegularity

private theorem compact_kernel_norm_convolution_continuous
    {κ ρ : Plane → ℝ} (hκ : Continuous κ) (hcκ : HasCompactSupport κ)
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    Continuous ((fun x => ‖κ x‖) ⋆[mul ℝ ℝ, volume] fun x => ‖ρ x‖) :=
  hcρ.norm.continuous_convolution_right (mul ℝ ℝ)
    ((hκ.integrable_of_hasCompactSupport hcκ).norm.locallyIntegrable) hρ.norm

/-- Associativity is valid pointwise for an L² field and two compact
continuous scalar kernels. The norm integrability requirements of Fubini
are proved from compact support, rather than added as hypotheses. -/
theorem convolution_compact_scalar_assoc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u : Plane → E} (hu : MemLp u 2 volume)
    {κ ρ : Plane → ℝ} (hκ : Continuous κ) (hcκ : HasCompactSupport κ)
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (x : Plane) :
    ((u ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip, volume] κ)
        ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip, volume] ρ) x =
      (u ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip, volume]
        (κ ⋆[mul ℝ ℝ, volume] ρ)) x := by
  let L := (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip
  apply convolution_assoc L L L (mul ℝ ℝ)
    (fun a b c => by simp [L, smul_smul, mul_comm]) hu.1
    hκ.aestronglyMeasurable hρ.aestronglyMeasurable
  · exact ae_of_all _ fun y =>
      hcκ.convolutionExists_right L (hu.locallyIntegrable (by norm_num)) hκ y
  · exact ae_of_all _ fun y =>
      hcρ.norm.convolutionExists_right (mul ℝ ℝ)
        ((hκ.integrable_of_hasCompactSupport hcκ).norm.locallyIntegrable) hρ.norm y
  · have hcn : HasCompactSupport
        ((fun y => ‖κ y‖) ⋆[mul ℝ ℝ, volume] fun y => ‖ρ y‖) :=
      hcκ.norm.convolution (mul ℝ ℝ) hcρ.norm
    exact hcn.convolutionExists_right (mul ℝ ℝ)
      ((hu.norm).locallyIntegrable (by norm_num))
      (compact_kernel_norm_convolution_continuous hκ hcκ hρ hcρ) x

/-- Two compact scalar smoothing kernels can be exchanged pointwise even
when the vector field is only an L² equivalence-class representative. -/
theorem convolution_compact_scalar_commute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u : Plane → E} (hu : MemLp u 2 volume)
    {κ ρ : Plane → ℝ} (hκ : Continuous κ) (hcκ : HasCompactSupport κ)
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (x : Plane) :
    ((u ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip, volume] κ)
        ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip, volume] ρ) x =
      ((u ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip, volume] ρ)
        ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip, volume] κ) x := by
  rw [convolution_compact_scalar_assoc hu hκ hcκ hρ hcρ,
    convolution_compact_scalar_assoc hu hρ hcρ hκ hcκ]
  have hflip : (mul ℝ ℝ).flip = mul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm _ _
  congr 1
  simpa only [hflip] using
    (convolution_flip (L := mul ℝ ℝ) (f := κ) (g := ρ) (μ := volume)).symm

/-- Commutation stated in the concrete gradient-smoothing notation. -/
theorem mollifyGradient_commute {g : Plane → Plane} (hg : MemLp g 2 volume)
    {κ ρ : Plane → ℝ} (hκ : Continuous κ) (hcκ : HasCompactSupport κ)
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (x : Plane) :
    mollifyGradient (mollifyGradient g κ) ρ x =
      mollifyGradient (mollifyGradient g ρ) κ x :=
  convolution_compact_scalar_commute hg hκ hcκ hρ hcρ x

end Torsion.WeakHarmonicRegularity

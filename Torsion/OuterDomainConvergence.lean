module

public import Torsion.DirichletGalerkin
public import Torsion.DilationWeak

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Strong weak-torsion convergence under outer dilation sandwiches

The error of two nested weak torsion gradients has squared L² norm equal
to the difference of their torsional rigidities. Physical dilation scales
that rigidity by the fourth power. Consequently outer domains squeezed
between a domain and dilations tending to scale one have strongly convergent
gradients. No boundary trace, Rellich theorem or boundary smoothness is used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Pointwise Topology ENNReal

namespace Torsion

/-- The global Dirichlet energy equals the integral of the actual weak
torsion value. -/
theorem IsWeakTorsion.norm_gradient_sq_eq_integral {D : Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hD : MeasurableSet D) :
    ‖hu.1.2.1.toLp g‖ ^ 2 = ∫ x, u x := by
  rw [← real_inner_self_eq_norm_sq]
  exact hu.global_weak_equation hD hu.1

/-- For nested domains, the actual global squared L² gradient error is the
exact difference of torsional rigidities. -/
theorem IsWeakTorsion.norm_gradient_sub_sq_eq_integral_sub {D E : Set Plane}
    {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hv : IsWeakTorsion E v h)
    (hD : MeasurableSet D) (hE : MeasurableSet E) (hDE : D ⊆ E) :
    ‖hv.1.2.1.toLp h - hu.1.2.1.toLp g‖ ^ 2 = (∫ x, v x) - ∫ x, u x := by
  rw [norm_sub_sq_real, hv.norm_gradient_sq_eq_integral hE,
    hu.norm_gradient_sq_eq_integral hD]
  rw [hv.global_weak_equation hE (hu.1.mono hDE)]
  ring

/-- Domain monotonicity of actual torsional rigidity follows directly from
Galerkin orthogonality; no pointwise representative is needed. -/
theorem IsWeakTorsion.integral_mono_of_subset {D E : Set Plane}
    {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hv : IsWeakTorsion E v h)
    (hD : MeasurableSet D) (hE : MeasurableSet E) (hDE : D ⊆ E) :
    (∫ x, u x) ≤ ∫ x, v x := by
  have he := hu.norm_gradient_sub_sq_eq_integral_sub hv hD hE hDE
  nlinarith [sq_nonneg ‖hv.1.2.1.toLp h - hu.1.2.1.toLp g‖]

/-- The global integral of a torsion-scaled function has degree four in the
physical length scale, in two dimensions. -/
theorem integral_scaledValue_volume (s : ℝ) (hs : s ≠ 0) (u : Plane → ℝ) :
    (∫ x, scaledValue s u x) = s ^ 4 * ∫ x, u x := by
  have h := integral_comp_inv_smul s hs u Set.univ
  simp only [smul_set_univ₀ hs, Measure.restrict_univ] at h
  simp only [scaledValue, integral_const_mul, h]
  ring

/-- The actual gradient error for an outer domain is bounded quantitatively
by a containing physical dilation. The intermediate domain need not be
convex, marked, smooth or nested in any other intermediate domain. -/
theorem IsWeakTorsion.norm_gradient_sub_sq_le_dilation
    {D E : Set Plane} {u v : Plane → ℝ} {g h : Plane → Plane}
    (hu : IsWeakTorsion D u g) (hv : IsWeakTorsion E v h)
    (hD : IsOpen D) (hE : IsOpen E)
    (s : ℝ) (hs : 0 < s) (hDE : D ⊆ E) (hEsD : E ⊆ s • D) :
    ‖hv.1.2.1.toLp h - hu.1.2.1.toLp g‖ ^ 2 ≤
      (s ^ 4 - 1) * ∫ x, u x := by
  have hmono := hv.integral_mono_of_subset (hu.dilate s hs) hE.measurableSet
    (hD.smul₀ hs.ne').measurableSet hEsD
  rw [integral_scaledValue_volume s hs.ne'] at hmono
  rw [hu.norm_gradient_sub_sq_eq_integral_sub hv hD.measurableSet hE.measurableSet hDE]
  nlinarith

/-- Actual outer-domain weak torsion gradients converge strongly in L²
under physical dilation sandwiches with scales tending to one. -/
theorem IsWeakTorsion.tendsto_eLpNorm_gradient_of_outer_dilation
    {D : Set Plane} {E : ℕ → Set Plane}
    {u : Plane → ℝ} {g : Plane → Plane}
    {v : ℕ → Plane → ℝ} {h : ℕ → Plane → Plane}
    (hu : IsWeakTorsion D u g) (hv : ∀ n, IsWeakTorsion (E n) (v n) (h n))
    (hD : IsOpen D) (hE : ∀ n, IsOpen (E n))
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hslim : Tendsto s atTop (𝓝 1))
    (hDE : ∀ n, D ⊆ E n) (hEsD : ∀ n, E n ⊆ s n • D) :
    Tendsto (fun n => eLpNorm (fun x => h n x - g x) 2 volume) atTop (𝓝 0) := by
  let H : ℕ → Lp Plane 2 (volume : Measure Plane) := fun n => (hv n).1.2.1.toLp (h n)
  let G : Lp Plane 2 (volume : Measure Plane) := hu.1.2.1.toLp g
  have hsq : Tendsto (fun n => ‖H n - G‖ ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => (s n ^ 4 - 1) * ∫ x, u x) atTop (𝓝 0) := by
      simpa using ((hslim.pow 4).sub_const 1).mul_const (∫ x, u x)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => sq_nonneg _) (fun n => ?_)
    exact hu.norm_gradient_sub_sq_le_dilation (hv n) hD (hE n) (s n) (hs n)
      (hDE n) (hEsD n)
  have hn : Tendsto (fun n => ‖H n - G‖) atTop (𝓝 0) := by
    have hh := hsq.sqrt
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh
  have hdist : Tendsto H atTop (𝓝 G) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [dist_eq_norm] using hn
  have hed := tendsto_iff_edist_tendsto_0.mp hdist
  simpa only [H, G, Lp.edist_toLp_toLp] using hed

end Torsion

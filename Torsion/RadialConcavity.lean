import Torsion.Hessian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# Homogeneity, supermodularity, and radial concavity

Finite-dimensional analytic tools for Lemma 3.4 of the source writeup.
-/

namespace Torsion.RadialConcavity

open Set Filter
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Vec (ι : Type*) := ι → ℝ

def positiveOrthant : Set (Vec ι) := {x | ∀ i, 0 < x i}

def Homogeneous (F : Vec ι → ℝ) : Prop :=
  ∀ (x : Vec ι), x ∈ positiveOrthant → ∀ t : ℝ, 0 < t → F (t • x) = t * F x

def Supermodular (F : Vec ι → ℝ) : Prop :=
  ∀ x ∈ positiveOrthant, ∀ y ∈ positiveOrthant,
    F x + F y ≤ F (x ⊔ y) + F (x ⊓ y)

def basis (i : ι) : Vec ι := Pi.single i 1

omit [DecidableEq ι] in
theorem isOpen_positiveOrthant : IsOpen (positiveOrthant : Set (Vec ι)) := by
  have : positiveOrthant = ⋂ i : ι, {x : Vec ι | 0 < x i} := by
    ext x
    simp [positiveOrthant]
  rw [this]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (continuous_apply i)

omit [Fintype ι] [DecidableEq ι] in
theorem convex_positiveOrthant : Convex ℝ (positiveOrthant : Set (Vec ι)) := by
  intro x hx y hy a b ha hb hab i
  change 0 < a * x i + b * y i
  by_cases hapos : 0 < a
  · exact add_pos_of_pos_of_nonneg (mul_pos hapos (hx i)) (mul_nonneg hb (hy i).le)
  · have hbpos : 0 < b := by linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha (hx i).le) (mul_pos hbpos (hy i))

omit [Fintype ι] in
private theorem positive_add_basis {x : Vec ι} (hx : x ∈ positiveOrthant)
    (i : ι) {t : ℝ} (ht : 0 ≤ t) : x + t • basis i ∈ positiveOrthant := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [basis, Pi.single_apply] using add_pos_of_pos_of_nonneg (hx i) ht
  · simpa [basis, Pi.single_apply, hji] using hx j

omit [DecidableEq ι] in
private theorem hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec ι → E} {df : Vec ι →L[ℝ] E} {x : Vec ι}
    (hf : HasFDerivAt f df x) (v : Vec ι) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (df v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  simpa using (show HasFDerivAt f df (x + (0 : ℝ) • v) by simpa using hf).comp_hasDerivAt 0 hl

private theorem deriv_nonneg_of_right {g : ℝ → ℝ} {d : ℝ}
    (hg : HasDerivAt g d 0) (hge : ∀ t : ℝ, 0 < t → g 0 ≤ g t) : 0 ≤ d := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hg.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 ≤ t⁻¹ * (g (0 + t) - g 0)
  simpa using mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hge t ht))

omit [DecidableEq ι] in
/-- Euler's identity is derived from the homogeneity equation by ordinary
one-variable differentiation along a ray. -/
theorem euler_identity {F : Vec ι → ℝ} (hhom : Homogeneous F)
    (hf : ∀ x ∈ positiveOrthant, DifferentiableAt ℝ F x)
    {x : Vec ι} (hx : x ∈ positiveOrthant) :
    fderiv ℝ F x x = F x := by
  have hl : HasDerivAt (fun t : ℝ => F (t • x)) (fderiv ℝ F x x) 1 := by
    have hf' : HasFDerivAt F (fderiv ℝ F x) ((1 : ℝ) • x) := by simpa using (hf x hx).hasFDerivAt
    simpa using hf'.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have hr : HasDerivAt (fun t : ℝ => F (t • x)) (F x) 1 := by
    have hr' : HasDerivAt (fun t : ℝ => t * F x) (F x) 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).mul_const (F x))
    apply hr'.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hhom x hx t ht
  exact hl.unique hr

omit [DecidableEq ι] in
/-- Differentiating Euler's identity gives a null vector of the Hessian.
All differentiability assumptions here concern the actual Fréchet derivative. -/
theorem hessian_null_vector {F : Vec ι → ℝ} (hhom : Homogeneous F)
    (hf : ∀ x ∈ positiveOrthant, DifferentiableAt ℝ F x)
    (hdf : ∀ x ∈ positiveOrthant, DifferentiableAt ℝ (fderiv ℝ F) x)
    {x : Vec ι} (hx : x ∈ positiveOrthant) (v : Vec ι) :
    fderiv ℝ (fderiv ℝ F) x v x = 0 := by
  have heuler : (fun y : Vec ι => fderiv ℝ F y y) =ᶠ[𝓝 x] F := by
    filter_upwards [isOpen_positiveOrthant.mem_nhds hx] with y hy
    exact euler_identity hhom hf hy
  have hh := ((hdf x hx).hasFDerivAt.clm_apply (hasFDerivAt_id x)).congr_of_eventuallyEq
    heuler.symm
  have heq := hh.unique (hf x hx).hasFDerivAt
  have hev := congrArg (fun L : Vec ι →L[ℝ] ℝ => L v) heq
  change fderiv ℝ F x v + fderiv ℝ (fderiv ℝ F) x v x = fderiv ℝ F x v at hev
  linarith

omit [Fintype ι] in
private theorem rectangle_inequality {F : Vec ι → ℝ} (hsuper : Supermodular F)
    {x : Vec ι} (hx : x ∈ positiveOrthant) {i j : ι} (hij : i ≠ j)
    {h k : ℝ} (hh : 0 ≤ h) (hk : 0 ≤ k) :
    F (x + h • basis i) + F (x + k • basis j) ≤
      F (x + k • basis j + h • basis i) + F x := by
  have hjoin : (x + h • basis i) ⊔ (x + k • basis j) =
      x + k • basis j + h • basis i := by
    ext l
    by_cases hli : l = i
    · subst l
      simp [basis, Pi.single_apply, hij, Ne.symm hij, max_eq_left hh, hh]
    · by_cases hlj : l = j
      · subst l
        simp [basis, Pi.single_apply, hij, Ne.symm hij, max_eq_right hk, hk]
      · simp [basis, Pi.single_apply, hli, hlj]
  have hmeet : (x + h • basis i) ⊓ (x + k • basis j) = x := by
    ext l
    by_cases hli : l = i
    · subst l
      simp [basis, Pi.single_apply, hij, Ne.symm hij, min_eq_right hh, hh]
    · by_cases hlj : l = j
      · subst l
        simp [basis, Pi.single_apply, hij, Ne.symm hij, min_eq_left hk, hk]
      · simp [basis, Pi.single_apply, hli, hlj]
  simpa only [hjoin, hmeet] using hsuper _ (positive_add_basis hx i hh)
    _ (positive_add_basis hx j hk)

/-- Supermodularity implies that each first partial derivative is increasing
when a distinct coordinate is increased. No second derivative is assumed. -/
theorem partial_derivative_mono {F : Vec ι → ℝ} (hsuper : Supermodular F)
    (hf : ∀ x ∈ positiveOrthant, DifferentiableAt ℝ F x)
    {x : Vec ι} (hx : x ∈ positiveOrthant) {i j : ι} (hij : i ≠ j)
    {k : ℝ} (hk : 0 ≤ k) :
    fderiv ℝ F x (basis i) ≤ fderiv ℝ F (x + k • basis j) (basis i) := by
  have hy := positive_add_basis hx j hk
  have hder := (hasDerivAt_line (hf _ hy).hasFDerivAt (basis i)).sub
    (hasDerivAt_line (hf _ hx).hasFDerivAt (basis i))
  have hnonneg := deriv_nonneg_of_right hder (by
    intro h hh
    have hrectangle := rectangle_inequality hsuper hx hij hh.le hk
    simp only [zero_smul, add_zero]
    linarith)
  linarith

/-- The off-diagonal signs of the Hessian are consequences of supermodularity,
proved by two successive one-sided differentiations of the lattice inequality. -/
theorem hessian_offdiag_nonneg {F : Vec ι → ℝ} (hsuper : Supermodular F)
    (hf : ∀ x ∈ positiveOrthant, DifferentiableAt ℝ F x)
    (hdf : ∀ x ∈ positiveOrthant, DifferentiableAt ℝ (fderiv ℝ F) x)
    {x : Vec ι} (hx : x ∈ positiveOrthant) {i j : ι} (hij : i ≠ j) :
    0 ≤ fderiv ℝ (fderiv ℝ F) x (basis j) (basis i) := by
  have hder := (hasDerivAt_line (hdf _ hx).hasFDerivAt (basis j)).clm_apply
    (hasDerivAt_const (0 : ℝ) (basis i))
  have hder' : HasDerivAt (fun t : ℝ => fderiv ℝ F (x + t • basis j) (basis i))
      (fderiv ℝ (fderiv ℝ F) x (basis j) (basis i)) 0 := by
    simpa using hder
  apply deriv_nonneg_of_right hder'
  intro k hk
  simpa using partial_derivative_mono hsuper hf hx hij hk.le



private theorem sum_basis (v : Vec ι) : ∑ i, v i • basis i = v := by
  ext j
  simp [basis, Finset.sum_apply, Pi.single_apply, eq_comm]

private theorem linear_expansion (L : Vec ι →L[ℝ] ℝ) (v : Vec ι) :
    L v = ∑ i, v i * L (basis i) := by
  conv_lhs => rw [← sum_basis v]
  simp

private theorem bilinear_expansion (B : Vec ι →L[ℝ] Vec ι →L[ℝ] ℝ) (v : Vec ι) :
    B v v = ∑ i, ∑ j, v i * B (basis i) (basis j) * v j := by
  conv_lhs => rw [← sum_basis v]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The actual Hessian of a twice continuously differentiable, homogeneous,
supermodular function is negative semidefinite on the positive orthant.
Symmetry, the null vector, and the off-diagonal signs are proved here rather
than passed as independent hypotheses. -/
theorem hessian_nonpos_of_contDiff {F : Vec ι → ℝ}
    (hC2 : ContDiffOn ℝ 2 F positiveOrthant)
    (hhom : Homogeneous F) (hsuper : Supermodular F)
    {x : Vec ι} (hx : x ∈ positiveOrthant) (v : Vec ι) :
    fderiv ℝ (fderiv ℝ F) x v v ≤ 0 := by
  have hC2at : ∀ y ∈ positiveOrthant, ContDiffAt ℝ 2 F y := fun y hy =>
    hC2.contDiffAt (isOpen_positiveOrthant.mem_nhds hy)
  have hf : ∀ y ∈ positiveOrthant, DifferentiableAt ℝ F y := fun y hy =>
    (hC2at y hy).differentiableAt (by norm_num)
  have hdf : ∀ y ∈ positiveOrthant, DifferentiableAt ℝ (fderiv ℝ F) y := fun y hy =>
    ((hC2at y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let B := fderiv ℝ (fderiv ℝ F) x
  let H := fun i j => B (basis i) (basis j)
  have hsymm : ∀ i j, H i j = H j i := by
    intro i j
    exact (hC2at x hx).isSymmSndFDerivAt (by norm_num [minSmoothness]) _ _
  have hnull : ∀ i, ∑ j, H i j * x j = 0 := by
    intro i
    have hn := hessian_null_vector hhom hf hdf hx (basis i)
    change B (basis i) x = 0 at hn
    rw [linear_expansion] at hn
    simpa [H, mul_comm] using hn
  have hoff : ∀ i j, i ≠ j → 0 ≤ H i j := by
    intro i j hij
    exact hessian_offdiag_nonneg hsuper hf hdf hx (Ne.symm hij)
  have hq := Hessian.quadratic_form_nonpos H x hsymm hx hoff hnull v
  rw [← bilinear_expansion] at hq
  exact hq

omit [DecidableEq ι] in
private theorem hasDerivAt_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec ι → E} {df : Vec ι →L[ℝ] E} (x v : Vec ι) (t : ℝ)
    (hf : HasFDerivAt f df (x + t • v)) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (df v) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact hf.comp_hasDerivAt t hl

omit [DecidableEq ι] in
/-- A negative semidefinite actual Hessian implies concavity. This proof
restricts to each closed line segment and applies the one-dimensional theorem
for nonpositive second derivatives. -/
theorem concave_of_hessian_nonpos {F : Vec ι → ℝ}
    (hf : ∀ x ∈ positiveOrthant, DifferentiableAt ℝ F x)
    (hdf : ∀ x ∈ positiveOrthant, DifferentiableAt ℝ (fderiv ℝ F) x)
    (hessian : ∀ x ∈ positiveOrthant, ∀ v : Vec ι,
      fderiv ℝ (fderiv ℝ F) x v v ≤ 0) :
    ConcaveOn ℝ positiveOrthant F := by
  refine ⟨convex_positiveOrthant, ?_⟩
  intro x hx y hy a b ha hb hab
  let v := y - x
  let line := fun t : ℝ => x + t • v
  let g := fun t : ℝ => F (line t)
  let dg := fun t : ℝ => fderiv ℝ F (line t) v
  let ddg := fun t : ℝ => fderiv ℝ (fderiv ℝ F) (line t) v v
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, line t ∈ positiveOrthant := by
    intro t ht
    have hm := convex_positiveOrthant hx hy (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    have hline : (1 - t) • x + t • y = line t := by
      ext i
      simp [line, v, smul_eq_mul]
      ring
    rwa [hline] at hm
  have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (dg t) t := by
    intro t ht
    exact hasDerivAt_affine x v t (hf _ (hmem t ht)).hasFDerivAt
  have hdg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt dg (ddg t) t := by
    intro t ht
    have hcomp := (hasDerivAt_affine x v t (hdf _ (hmem t ht)).hasFDerivAt).clm_apply
      (hasDerivAt_const t v)
    simpa [dg, ddg, line] using hcomp
  have hgc : ConcaveOn ℝ (Icc (0 : ℝ) 1) g := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (f' := dg) (f'' := ddg)
    · intro t ht
      exact (hg t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact (hdg t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact hessian _ (hmem t (interior_subset ht)) v
  have hineq := hgc.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ha hb hab
  have hzero : g 0 = F x := by simp [g, line]
  have hone : g 1 = F y := by simp [g, line, v]
  have hab' : a • (0 : ℝ) + b • (1 : ℝ) = b := by simp
  have hbline : g b = F (a • x + b • y) := by
    apply congrArg F
    ext i
    simp [line, v, smul_eq_mul]
    have ha' : a = 1 - b := by linarith
    rw [ha']
    ring
  rwa [hzero, hone, hab', hbline] at hineq

/-- The smooth case of Lemma 3.4: degree-one homogeneity and supermodularity
imply concavity on the positive orthant for a `C²` function. -/
theorem concave_of_contDiff_homogeneous_supermodular {F : Vec ι → ℝ}
    (hC2 : ContDiffOn ℝ 2 F positiveOrthant)
    (hhom : Homogeneous F) (hsuper : Supermodular F) :
    ConcaveOn ℝ positiveOrthant F := by
  apply concave_of_hessian_nonpos
  · intro x hx
    exact (hC2.contDiffAt (isOpen_positiveOrthant.mem_nhds hx)).differentiableAt (by norm_num)
  · intro x hx
    exact ((hC2.contDiffAt (isOpen_positiveOrthant.mem_nhds hx)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  · intro x hx v
    exact hessian_nonpos_of_contDiff hC2 hhom hsuper hx v

end Torsion.RadialConcavity

module

public import Torsion.CauchyConformalGeometry.Convexity
public import Torsion.CauchyConformalGeometry.MarkedGeometry
public import Torsion.ContinuousProfiles
public import Torsion.CauchyRadialProfile
public import Torsion.CauchyImageAreaExact
public import Torsion.PhysicalCauchyMarkedFlux

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual radial domain of the Cauchy image

Convexity and the constructed marked half-ball determine the intersection
with every upper ray: it is exactly the interval before the actual frontier
point. This identifies the positive continuous angular profile with the
original Cauchy image, rather than assuming a radial representation.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Torsion

/-- Every positive upper ray has actual points of a marked domain
arbitrarily close to its marked origin. -/
theorem IsMarked.exists_small_ray_point {D : Set Plane} (hD : IsMarked D)
    {e : Plane} (he : 0 < e.im) (hn : ‖e‖ = 1) {r : ℝ} (hr : 0 < r) :
    ∃ s : ℝ, 0 < s ∧ s < r ∧ (s : ℂ) * e ∈ D := by
  obtain ⟨ρ, hρ, hflat⟩ := hD.2.2.2
  let s : ℝ := min r ρ / 2
  have hs : 0 < s := half_pos (lt_min hr hρ)
  have hsr : s < r := (half_lt_self (lt_min hr hρ)).trans_le (min_le_left r ρ)
  have hsρ : s < ρ := (half_lt_self (lt_min hr hρ)).trans_le (min_le_right r ρ)
  have hp : (s : ℂ) * e ∈ upperHalfPlane ∩ Metric.ball 0 ρ := by
    constructor
    · simpa only [upperHalfPlane, mem_setOf_eq, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero] using mul_pos hs he
    · simpa only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs, hn, mul_one] using hsρ
  rw [← hflat] at hp
  exact ⟨s, hs, hsr, hp.1⟩

private theorem ray_combo {e : Plane} {p q r : ℝ} (hpq : p ≠ q) :
    ((q - r) / (q - p)) • ((p : ℂ) * e) +
      ((r - p) / (q - p)) • ((q : ℂ) * e) = (r : ℂ) * e := by
  have hscalar : (q - r) / (q - p) * p + (r - p) / (q - p) * q = r := by
    field_simp [sub_ne_zero.mpr hpq.symm]
    ring
  simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    ← add_mul, ← Complex.ofReal_add, hscalar]

/-- On each upper ray of a convex marked domain, an actual positive
frontier point is precisely its radial endpoint. -/
theorem IsMarked.ray_mem_iff_lt_frontier_radius {D : Set Plane}
    (hD : IsMarked D) (hc : Convex ℝ D)
    {e : Plane} (he : 0 < e.im) (hn : ‖e‖ = 1)
    {R : ℝ} (hR : 0 < R) (hp : (R : ℂ) * e ∈ frontier D)
    {r : ℝ} (hr : 0 < r) :
    (r : ℂ) * e ∈ D ↔ r < R := by
  constructor
  · intro hmem
    by_contra hlt
    have hRr : R ≤ r := le_of_not_gt hlt
    obtain ⟨s, hs, hsR, hsmem⟩ := hD.exists_small_ray_point he hn hR
    have hsr : s < r := hsR.trans_le hRr
    have hden : 0 < r - s := sub_pos.2 hsr
    have hsum : (r - R) / (r - s) + (R - s) / (r - s) = 1 := by
      field_simp
    have hcomb := hc hsmem hmem
      (div_nonneg (sub_nonneg.2 hRr) hden.le)
      (div_nonneg (sub_nonneg.2 hsR.le) hden.le) hsum
    rw [ray_combo (ne_of_lt hsr)] at hcomb
    exact ((hD.1.frontier_eq ▸ hp).2) hcomb
  · intro hrR
    obtain ⟨s, hs, hsr, hsmem⟩ := hD.exists_small_ray_point he hn hr
    have hsR : s < R := hsr.trans hrR
    have hden : 0 < R - s := sub_pos.2 hsR
    have hsum : (R - r) / (R - s) + (r - s) / (R - s) = 1 := by
      field_simp
    have hcomb := hc.combo_interior_closure_mem_interior
      (show (s : ℂ) * e ∈ interior D from hD.1.interior_eq.symm ▸ hsmem)
      (frontier_subset_closure hp)
      (div_pos (sub_pos.2 hrR) hden)
      (div_nonneg (sub_nonneg.2 hsr.le) hden.le) hsum
    rw [ray_combo (ne_of_lt hsR), hD.1.interior_eq] at hcomb
    exact hcomb

/-- Actual frontier radii of a convex marked domain give its exact original
radial set, using the usual continuous-profile extension. -/
theorem IsMarked.radialDomain_eq_of_frontier_radii {D : Set Plane}
    (hD : IsMarked D) (hc : Convex ℝ D) (R : ContinuousProfiles.Profile)
    (hR : ∀ θ, 0 < R θ)
    (hfront : ∀ θ : ContinuousProfiles.Angle,
      0 < (θ : ℝ) → (θ : ℝ) < Real.pi →
      ((R θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I) ∈ frontier D) :
    radialDomain (ContinuousProfiles.extend R) = D := by
  ext w
  by_cases hwH : 0 < w.im
  · have harg : w.arg ∈ Ioo (0 : ℝ) Real.pi := by
      constructor
      · refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hwH.le) ?_
        intro h
        have him := (Complex.arg_eq_zero_iff.mp h.symm).2
        linarith
      · exact Complex.arg_lt_pi_iff.mpr (Or.inr hwH.ne')
    let θ : ContinuousProfiles.Angle := ⟨w.arg, Ioo_subset_Icc_self harg⟩
    let e : Plane := Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
    have he : 0 < e.im := by
      simpa [e, Complex.exp_mul_I, θ] using
        Real.sin_pos_of_pos_of_lt_pi harg.1 harg.2
    have hn : ‖e‖ = 1 := by dsimp [e]; exact Complex.norm_exp_ofReal_mul_I _
    have hp : ((R θ : ℝ) : ℂ) * e ∈ frontier D := hfront θ harg.1 harg.2
    have hwne : w ≠ 0 := by intro h; simp [h] at hwH
    have hmem := hD.ray_mem_iff_lt_frontier_radius hc he hn (hR θ) hp (norm_pos_iff.2 hwne)
    change (‖w‖ : ℂ) * Complex.exp ((w.arg : ℂ) * Complex.I) ∈ D ↔ ‖w‖ < R θ at hmem
    rw [Complex.norm_mul_exp_arg_mul_I] at hmem
    rw [RadialGeometry.mem_radialDomain_iff, and_iff_right hwH,
      show ContinuousProfiles.extend R w.arg = R θ from ContinuousProfiles.extend_coe R θ]
    exact hmem.symm
  · rw [RadialGeometry.mem_radialDomain_iff]
    constructor
    · intro h
      exact (hwH h.1).elim
    · intro h
      exact (hwH (hD.2.2.1 h)).elim

namespace Spectral

section Actual

variable {a b : ℝ} {φ : ℝ → ℝ} {C α : ℝ≥0}
variable (ha : 0 < a) (hφ : HolderWith C α φ) (hα0 : 0 < α) (hα1 : α ≤ 1)
variable (hodd : Function.Odd φ) (hzero : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
variable (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < φ x)
variable (hlinear : ∀ x ∈ Ioo (-1 : ℝ) 1,
  realCauchyBoundaryRe φ x = a * height φ x - b)
variable (hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) φ)
variable (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ φ x)

local notation "R" => cauchyRadialProfile ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd

/-- The positive continuous radial profile gives exactly the original
physical Cauchy image. Convexity and marked geometry are proved inputs,
not a radial-representation hypothesis. -/
theorem radialDomain_cauchyRadialProfile_eq :
    radialDomain (ContinuousProfiles.extend R) = cauchyImage φ := by
  apply (cauchyImage_isMarked hφ hα0 hα1 hodd hzero hpos).radialDomain_eq_of_frontier_radii
    (cauchyImage_convex ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd) R
    (cauchyRadialProfile_pos ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd)
  intro θ _ _
  rw [← cauchyRadialBoundary_eq_polar ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd θ]
  exact cauchyRadialBoundary_mem_frontier ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd θ

/-- The profile angular area is the exact geometric area already proved
for the original Cauchy image. -/
theorem radialArea_cauchyRadialProfile :
    radialArea (ContinuousProfiles.extend R) = a * squareMass φ / 2 := by
  have hpositive : ∀ θ ∈ Icc (0 : ℝ) Real.pi, 0 < ContinuousProfiles.extend R θ := by
    intro θ hθ
    rw [show ContinuousProfiles.extend R θ = R ⟨θ, hθ⟩ from
      ContinuousProfiles.extend_coe R ⟨θ, hθ⟩]
    exact cauchyRadialProfile_pos ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd ⟨θ, hθ⟩
  rw [← RadialGeometry.area_radialDomain (ContinuousProfiles.extend R).continuous.continuousOn hpositive,
    radialDomain_cauchyRadialProfile_eq ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd]
  exact area_cauchyImage_eq_half_squareMass ha.ne' hφ hα0 hα1 hodd hzero hpos hlinear

/-- The genuine angular L² norm of the actual radius is exactly `aN`. -/
theorem norm_sq_embed_cauchyRadialProfile :
    ‖ContinuousProfiles.embed R‖ ^ 2 = a * squareMass φ := by
  rw [ContinuousProfiles.norm_sq_eq_twice_radialArea,
    radialArea_cauchyRadialProfile ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd]
  ring

/-- The original radial-domain PDE flux is the exact spectral ratio. -/
theorem torsionFlux_cauchyRadialProfile :
    torsionFlux (radialDomain (ContinuousProfiles.extend R)) = b / a := by
  rw [radialDomain_cauchyRadialProfile_eq ha hφ hα0 hα1 hodd hzero hpos hlinear hc hd]
  exact torsionFlux_cauchyImage ha.ne' hφ hα0 hα1 hodd hzero hpos hlinear

end Actual
end Spectral
end Torsion

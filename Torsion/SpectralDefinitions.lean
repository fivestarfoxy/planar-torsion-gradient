module

public import Torsion.Definitions
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Restricted half-Laplacian and Cauchy construction: definitions

The Fourier convention is exactly that of Section 1: exp(-i x ξ), with the
factor 1/(2π) in the form. The form domain is the closure of C∞_c(-1,1),
not the spectral square root of the ordinary Dirichlet Laplacian.

No existence, simplicity, ordering, sign, Hölder regularity, or concavity
of an eigenfunction is proved in this module.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Torsion.Spectral

/-- Fourier transform with the convention in the attached writeup. -/
def fourier (f : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) * (f x : ℂ)

/-- Integrability needed for the half-Laplacian form. -/
def FiniteEnergy (f : ℝ → ℝ) : Prop :=
  Integrable (fun ξ : ℝ => |ξ| * ‖fourier f ξ‖ ^ 2)

/-- The real bilinear form in Section 1. -/
def energy (f g : ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ ξ : ℝ, |ξ| * ((fourier f ξ) * star (fourier g ξ)).re

/-- The core of the restricted realization. -/
def IsCore (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo (-1) 1

/-- Closed restricted form domain, specified through its defining core.
The approximation is in L² and in the half-derivative energy norm. -/
def MemRestrictedFormDomain (f : ℝ → ℝ) : Prop :=
  MemLp f 2 volume ∧ FiniteEnergy f ∧
  (∀ᵐ x : ℝ, x ∉ Ioo (-1) 1 → f x = 0) ∧
  ∃ v : ℕ → ℝ → ℝ,
    (∀ n, IsCore (v n)) ∧
    Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 volume) atTop (𝓝 0) ∧
    Tendsto (fun n => energy (fun x => v n x - f x) (fun x => v n x - f x))
      atTop (𝓝 0)

/-- A nonzero weak eigenfunction for the restricted realization.
Nonzero means nonzero as an L² equivalence class, not merely at one point.
The ordering as the second eigenpair is a further spectral theorem. -/
def IsRestrictedEigenfunction (a : ℝ) (φ : ℝ → ℝ) : Prop :=
  MemRestrictedFormDomain φ ∧
  ¬ (φ =ᵐ[volume] fun _ => 0) ∧
  ∀ ψ : ℝ → ℝ, MemRestrictedFormDomain ψ →
    energy φ ψ = a * ∫ x : ℝ, φ x * ψ x

/-- Equation (1.2), including its zero exterior values. -/
def height (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  if |x| < 1 then ∫ s in Icc |x| 1, φ s else 0

/-- M in (1.3). -/
def mass (φ : ℝ → ℝ) : ℝ := ∫ x in Icc (-1) 1, height φ x

/-- N in (1.3). -/
def squareMass (φ : ℝ → ℝ) : ℝ := ∫ x in Icc (-1) 1, (height φ x) ^ 2

/-- Equation (1.4). The formula is defined everywhere; all analytic claims
about it are restricted to `upperHalfPlane`. -/
def cauchy (φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  -((Real.pi : ℂ)⁻¹) *
    ∫ s in Icc (-1 : ℝ) 1, (height φ s : ℂ) / (z - (s : ℂ))

/-- The auxiliary holomorphic transform (5.3). -/
def auxiliary (φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  -((2 * Real.pi : ℂ)⁻¹) *
    ∫ s in Icc (-1 : ℝ) 1, ((height φ s) ^ 2 : ℝ) / (z - (s : ℂ))

end Torsion.Spectral

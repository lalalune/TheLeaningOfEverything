/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import QuantumMechanics.SpectralTheory.FunctionalCalc.Algebraic
/-!
# Generator Recovery from Spectral Measure

This file packages consequences of a spectral measure for a self-adjoint generator
`A`. Given the corresponding inner-product identity and domain inclusions, it
derives `A = ∫ s dE(s)` on the domain of `A` and identifies the domain with
`{ψ : ∫|s|² dμ_ψ < ∞}`.

## Main definitions

* `IsSpectralMeasureFor`: Predicate bundling spectral measure laws for a generator
* `identityFunction`: The function `id(s) = s`

## Main results

* `generator_eq_spectral_integral`: `A = ∫ s dE(s)` on `dom(A)`, from the
  corresponding inner-product identity
* `generator_domain_eq_functional_domain`: `dom(A) = {ψ : ∫|s|² dμ_ψ < ∞}`,
  from the two domain inclusions

## Tags

generator, spectral measure, spectral theorem, domain characterization
-/

namespace FunctionalCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge.Resolvent SpectralBridge.Bochner QuantumMechanics.Generators ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## IsSpectralMeasureFor
-/

/-- Predicate: E is the spectral measure associated to the generator -/
structure IsSpectralMeasureFor (E : Set ℝ → H →L[ℂ] H)
    {U_grp : OneParameterUnitaryGroup (H := H)} (gen : Generator U_grp) : Prop where
  proj_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C)
  proj_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ
  proj_empty : E ∅ = 0
  proj_univ : E Set.univ = 1
  proj_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
             E (B ∪ C) = E B + E C
  proj_sot : ∀ ψ t₀, Filter.Tendsto (fun t => E (Set.Iic t) ψ) (nhdsWithin t₀ (Set.Ioi t₀)) (nhds (E (Set.Iic t₀) ψ))
  proj_σ_add : ∀ ψ (B : ℕ → Set ℝ), (∀ n, MeasurableSet (B n)) →
        (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
        HasSum (fun n => E (B n) ψ) (E (⋃ n, B n) ψ)
  unitary_eq_integral : ∀ (t : ℝ) (ψ : H),
    ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ s, Complex.exp (I * t * s) ∂(spectral_scalar_measure E ψ ⟨proj_mul, proj_sa, proj_sot, proj_empty, proj_univ, proj_add, proj_σ_add⟩)

/-- Extract IsSpectralMeasure from IsSpectralMeasureFor -/
def IsSpectralMeasureFor.toIsSpectralMeasure {E : Set ℝ → H →L[ℂ] H}
    {U_grp : OneParameterUnitaryGroup (H := H)} {gen : Generator U_grp}
    (hE : IsSpectralMeasureFor E gen) : IsSpectralMeasure E where
  mul := hE.proj_mul
  sa := hE.proj_sa
  sot := hE.proj_sot
  add := hE.proj_add
  empty := hE.proj_empty
  univ := hE.proj_univ
  σ_add := hE.proj_σ_add

/-!
## Identity Function
-/

/-- The identity function id(s) = s -/
def identityFunction : ℝ → ℂ := fun s => s

/-!
## Main Theorems
-/

/-- Recover `A = ∫ s dE(s)` on `dom(A)` from the inner-product identity.

The generator equals the functional calculus of the identity function for this
vector. -/
theorem generator_eq_spectral_integral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ_dom : ψ ∈ gen.domain)
    (hψ_func : ψ ∈ functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction)
    (hinner : ∀ φ : H,
      ⟪gen.op ⟨ψ, hψ_dom⟩, φ⟫_ℂ = ⟪spectral_integral E hE.toIsSpectralMeasure identityFunction ψ hψ_func, φ⟫_ℂ) :
    gen.op ⟨ψ, hψ_dom⟩ = functionalCalculus E hE.toIsSpectralMeasure hE.proj_univ identityFunction ⟨ψ, hψ_func⟩ := by
  apply ext_inner_right ℂ
  intro φ
  exact hinner φ

/-- Domain equality: dom(A) = dom(id(A)) -/
theorem generator_domain_eq_functional_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (hsubset : ∀ ψ : H, ψ ∈ gen.domain →
      ψ ∈ functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction)
    (hsupset : ∀ ψ : H, ψ ∈ functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction →
      ψ ∈ gen.domain) :
    (gen.domain : Set H) = functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction := by
  ext ψ
  constructor
  · exact hsubset ψ
  · exact hsupset ψ

/-- Package a uniform functional-domain bound into `dom(A) ⊆ dom(f(A))`. -/
theorem generator_domain_subset_functional {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (hf : ∃ C n : ℝ, ∀ s, ‖f s‖ ≤ C * (1 + |s|)^n)
    (haux : ∀ (C n : ℝ) (hCn : ∀ s, ‖f s‖ ≤ C * (1 + |s|)^n) (ψ : H), ψ ∈ gen.domain →
      ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    (gen.domain : Set H) ⊆ functionalDomain (spectral_scalar_measure E · hE) f := by
  intro ψ hψ
  obtain ⟨C, n, hCn⟩ := hf
  exact haux C n hCn ψ hψ

end FunctionalCalculus

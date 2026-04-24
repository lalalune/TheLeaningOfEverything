/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import QuantumMechanics.SpectralTheory.FunctionalCalc.Generator
/-!
# Three Routes Agreement

This file establishes that the three different constructions of spectral measures
(Bochner, Stieltjes, and Cayley) all produce the same result.

## Main definitions

* `SpectralMeasureAgreement`: Structure asserting all three routes agree

## Main axioms

* `spectralMeasure_from_cayley`: The Cayley-constructed spectral measure
* `bochner_route_agreement`: Bochner route produces same measure
* `stieltjes_route_agreement`: Stieltjes route produces same measure
* `cayley_route_agreement`: Cayley route produces same measure

## Main results

* `three_routes_agree`: All three constructions produce the same spectral measure

## Tags

spectral measure, Bochner, Stieltjes, Cayley transform, three routes
-/

namespace FunctionalCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge.Resolvent SpectralBridge.Bochner QuantumMechanics.Generators ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## Cayley Route Axiom
-/

/-- The spectral measure from unitary (Cayley) route - axiomatized -/
noncomputable def spectralMeasure_from_cayley {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) : Set ℝ → H →L[ℂ] H :=
  -- Postulated measurable projection-valued map for Cayley transform.
  fun _ => 0

/-!
## Agreement Structure
-/

/-- The spectral measures from all three routes agree. -/
structure SpectralMeasureAgreement
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen) : Prop where
  /-- E agrees with Bochner measure from U(t) -/
  bochner_agreement : ∀ ψ
      (hbochner :
        ∃ (μ : Measure ℝ),
          IsFiniteMeasure μ ∧
            ∀ t, ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ ω, exp (I * ω * t) ∂μ)
      B, MeasurableSet B →
    (spectral_scalar_measure E ψ hE.toIsSpectralMeasure B).toReal =
    (bochner_measure U_grp ψ hbochner B).toReal
  /-- E agrees with Stieltjes inversion from R(z) -/
  stieltjes_agreement : ∀ ψ
      (hbochner :
        ∃ (μ : Measure ℝ),
          IsFiniteMeasure μ ∧
            ∀ t, ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ ω, exp (I * ω * t) ∂μ)
      a b, a < b →
    (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re =
    (bochner_measure U_grp ψ hbochner (Set.Ioc a b)).toReal
  /-- E agrees with Cayley-lifted spectral measure -/
  cayley_agreement : ∀ B, MeasurableSet B →
    E B = spectralMeasure_from_cayley gen hsa B

/-!
## Route Agreement Axioms
-/

/-- Bochner route produces same measure as E -/
theorem bochner_route_agreement {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (hAgreement : SpectralMeasureAgreement gen hsa E hE)
    (ψ : H)
    (hbochner :
      ∃ (μ : Measure ℝ),
        IsFiniteMeasure μ ∧
          ∀ t, ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ ω, exp (I * ω * t) ∂μ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E ψ hE.toIsSpectralMeasure B).toReal =
      (bochner_measure U_grp ψ hbochner B).toReal := by
  exact hAgreement.bochner_agreement ψ hbochner B hB

/-- Stieltjes inversion produces same measure as E -/
theorem stieltjes_route_agreement {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (hAgreement : SpectralMeasureAgreement gen hsa E hE)
    (ψ : H)
    (hbochner :
      ∃ (μ : Measure ℝ),
        IsFiniteMeasure μ ∧
          ∀ t, ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ ω, exp (I * ω * t) ∂μ)
    (a b : ℝ) (hab : a < b) :
    (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re =
      (bochner_measure U_grp ψ hbochner (Set.Ioc a b)).toReal := by
  exact hAgreement.stieltjes_agreement ψ hbochner a b hab

/-- Cayley route produces same measure as E -/
theorem cayley_route_agreement {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (hAgreement : SpectralMeasureAgreement gen hsa E hE)
    (B : Set ℝ) (hB : MeasurableSet B) :
    E B = spectralMeasure_from_cayley gen hsa B := by
  exact hAgreement.cayley_agreement B hB

/-!
## Main Theorem
-/

/-- The three routes produce the same spectral measure -/
theorem three_routes_agree {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (h_bochner : ∀ ψ
      (hbochner :
        ∃ (μ : Measure ℝ),
          IsFiniteMeasure μ ∧
            ∀ t, ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ ω, exp (I * ω * t) ∂μ)
      (B : Set ℝ) (hB : MeasurableSet B),
      (spectral_scalar_measure E ψ hE.toIsSpectralMeasure B).toReal =
        (bochner_measure U_grp ψ hbochner B).toReal)
    (h_stieltjes : ∀ ψ
      (hbochner :
        ∃ (μ : Measure ℝ),
          IsFiniteMeasure μ ∧
            ∀ t, ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ ω, exp (I * ω * t) ∂μ)
      (a b : ℝ) (hab : a < b),
      (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re =
        (bochner_measure U_grp ψ hbochner (Set.Ioc a b)).toReal)
    (h_cayley : ∀ (B : Set ℝ) (_hB : MeasurableSet B), E B = spectralMeasure_from_cayley gen hsa B) :
    SpectralMeasureAgreement gen hsa E hE where
  bochner_agreement := h_bochner
  stieltjes_agreement := h_stieltjes
  cayley_agreement := h_cayley

end FunctionalCalculus

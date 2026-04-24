/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Relativity.PauliMatrices.ToTensor
/-!

## Bispinors

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open OverColor.Discrete
open Fermion
noncomputable section
namespace complexLorentzTensor
open Lorentz
open PauliMatrix
/-!

## Definitions

-/
open TensorSpecies
open Tensor

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p^μ`. -/
def contrBispinorUp (p : ℂT[.up]) : ℂT[.upL, .upR] := permT id (PermCond.auto)
  {pauliCo | μ α β ⊗ p | μ}ᵀ

/-- Lower both spinor indices of a bispinor using the alternating metrics. -/
def lowerBisp (t : ℂT[.upL, .upR]) : ℂT[.downL, .downR] := permT id (PermCond.auto)
  {εL' | α α' ⊗ εR' | β β' ⊗ t | α β}ᵀ

/-- Raise both spinor indices of a bispinor using the alternating metrics. -/
def raiseBisp (t : ℂT[.downL, .downR]) : ℂT[.upL, .upR] :=
  permT ![0, 1] (by
    refine ⟨by decide, ?_⟩
    intro i
    fin_cases i <;> decide)
    ((contrT 2 1 3 (by simp; rfl)
      ((contrT 4 3 5 (by simp; rfl)
        ((prodT ((prodT (Tensorial.toTensor εL)) (Tensorial.toTensor εR)))
          (Tensorial.toTensor t))))) )

/-- A bispinor `pₐₐ` created from a lorentz vector `p^μ`. -/
def contrBispinorDown (p : ℂT[.up]) : ℂT[.downL, .downR] := lowerBisp (contrBispinorUp p)

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p_μ`. -/
def coBispinorUp (p : ℂT[.down]) : ℂT[.upL, .upR] := permT id (PermCond.auto)
  {σ^^^ | μ α β ⊗ p | μ}ᵀ

/-- A bispinor `pₐₐ` created from a lorentz vector `p_μ`. -/
def coBispinorDown (p : ℂT[.down]) : ℂT[.downL, .downR] := lowerBisp (coBispinorUp p)

@[simp]
lemma contrBispinorDown_eq_lowerBisp (p : ℂT[.up]) :
    contrBispinorDown p = lowerBisp (contrBispinorUp p) := rfl

@[simp]
lemma coBispinorDown_eq_lowerBisp (p : ℂT[.down]) :
    coBispinorDown p = lowerBisp (coBispinorUp p) := rfl

/-!

## Basic equalities.

-/

/-- `{contrBispinorUp p | α β = εL | α α' ⊗ εR | β β'⊗ contrBispinorDown p | α' β' }ᵀ`.

Proof: expand `contrBispinorDown` and use fact that metrics contract to the identity.
-/
informal_lemma contrBispinorUp_eq_metric_contr_contrBispinorDown where
  deps := [``contrBispinorUp, ``contrBispinorDown, ``leftMetric, ``rightMetric]
  tag := "6V2PV"

/-- `{coBispinorUp p | α β = εL | α α' ⊗ εR | β β'⊗ coBispinorDown p | α' β' }ᵀ`.

proof: expand `coBispinorDown` and use fact that metrics contract to the identity.
-/
informal_lemma coBispinorUp_eq_metric_contr_coBispinorDown where
  deps := [``coBispinorUp, ``coBispinorDown, ``leftMetric, ``rightMetric]
  tag := "6V2P6"

end complexLorentzTensor
end

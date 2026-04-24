/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Proj

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {f g : ℝ → ℝ}

noncomputable section

open scoped MatrixOrder ComplexOrder Matrix Kronecker

namespace HermitianMat

/-- The square root of a Hermitian matrix. Negative eigenvalues are mapped to zero. -/
noncomputable def sqrt (A : HermitianMat d 𝕜) : HermitianMat d 𝕜 :=
  A.cfc Real.sqrt

theorem sqrt_sq_eq_proj (A : HermitianMat d 𝕜) :
    A.sqrt.mat * A.sqrt.mat = A⁺ := by
  rw [sqrt, ← mat_cfc_mul, ← HermitianMat.ext_iff, posPart_eq_cfc_ite]
  congr! 2 with x
  grind [Pi.mul_apply, Real.mul_self_sqrt, Real.sqrt_eq_zero']

theorem sqrt_sq (hA : 0 ≤ A) :
    A.sqrt.mat * A.sqrt.mat = A := by
  rw [sqrt_sq_eq_proj]
  have hneg : -A ≤ 0 := by
    simpa using hA
  have hnegpart0 : (-A)⁺ = 0 := (posPart_eq_zero_iff (A := -A)).2 hneg
  have hnegpart : A⁻ = 0 := by
    rw [show A⁻ = (-A)⁺ by simpa using (neg_negPart_eq_posPart (A := -A))]
    exact hnegpart0
  have hAeq : A⁺ - A⁻ = A := posPart_add_negPart A
  rw [hnegpart, sub_zero] at hAeq
  simpa using congrArg HermitianMat.mat hAeq

theorem commute_sqrt_left (hAB : Commute A.mat B.mat) :
    Commute A.sqrt.mat B.mat := by
  simpa [sqrt] using hAB.cfc_left (f := Real.sqrt)

theorem commute_sqrt_right (hAB : Commute A.mat B.mat) :
    Commute A.mat B.sqrt.mat := by
  simpa [sqrt] using hAB.cfc_right (f := Real.sqrt)

theorem sqrt_nonneg (A : HermitianMat d 𝕜) : 0 ≤ A.sqrt := by
  rw [sqrt, zero_le_cfc]
  intro
  positivity

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat.sqrt` -/
@[positivity HermitianMat.sqrt _]
def evalHermitianMatSqrt : PositivityExt where eval {_u _α} _zα _pα e := do
  let .app _sqrt (A : Expr) ← whnfR e | throwError "not sqrt application"
  pure (.nonnegative (← mkAppM ``HermitianMat.sqrt_nonneg #[A]))

example {A : HermitianMat d ℂ} : 0 ≤ A.sqrt := by
  positivity

example [Nonempty d] {A : HermitianMat d ℂ} : 0 ≤ (1 + A.sqrt).sqrt := by
  positivity

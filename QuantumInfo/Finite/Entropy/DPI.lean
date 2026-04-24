/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.Relative
import QuantumInfo.ForMathlib.HermitianMat.CfcOrder
import QuantumInfo.ForMathlib.HermitianMat.Rpow

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace HermitianMat
open scoped Matrix ComplexOrder
open BigOperators

variable {d d₂ : Type*}
variable [Fintype d] [Fintype d₂]
variable [DecidableEq d] [DecidableEq d₂]
variable {σ : MState d}

/-!
# DPI

This file records the algebraic `Γ_σ` and `T = Γ_{Φ(σ)}⁻¹ ∘ Φ ∘ Γ_σ` infrastructure used in the
standard proof of data processing for sandwiched Rényi quantities.

The weighted Schatten norm interpolation argument itself is not yet formalized here, so this file
keeps only the part of the development that is currently proved and used.
-/

/-- The map `Γ_σ(X) = σ^{1/2} X σ^{1/2}`. -/
noncomputable def Gamma (σ : MState d) (X : Matrix d d ℂ) : Matrix d d ℂ :=
  (σ.M ^ (1 / 2 : ℝ)).mat * X * (σ.M ^ (1 / 2 : ℝ)).mat

/-- The inverse map `Γ_σ⁻¹(X) = σ^{-1/2} X σ^{-1/2}` on the support of a positive definite state. -/
noncomputable def Gamma_inv (σ : MState d) (X : Matrix d d ℂ) : Matrix d d ℂ :=
  (σ.M ^ (-1 / 2 : ℝ)).mat * X * (σ.M ^ (-1 / 2 : ℝ)).mat

/-- The operator `T = Γ_{Φ(σ)}⁻¹ ∘ Φ ∘ Γ_σ`. -/
noncomputable def T_op (Φ : CPTPMap d d₂) (σ : MState d) (X : Matrix d d ℂ) : Matrix d₂ d₂ ℂ :=
  Gamma_inv (Φ σ) (Φ.map (Gamma σ X))

/-- `Γ_σ` as a linear map. -/
noncomputable def Gamma_map (σ : MState d) : MatrixMap d d ℂ :=
  MatrixMap.conj (σ.M ^ (1 / 2 : ℝ)).mat

lemma Gamma_map_eq (σ : MState d) (X : Matrix d d ℂ) :
    Gamma_map σ X = Gamma σ X := by
  dsimp [Gamma_map, Gamma, MatrixMap.conj]
  rw [(σ.M ^ (1 / 2 : ℝ)).H.eq]

lemma Gamma_map_CP (σ : MState d) : (Gamma_map σ).IsCompletelyPositive := by
  simpa [Gamma_map] using MatrixMap.conj_isCompletelyPositive ((σ.M ^ (1 / 2 : ℝ)).mat)

/-- `Γ_σ⁻¹` as a linear map. -/
noncomputable def Gamma_inv_map (σ : MState d) : MatrixMap d d ℂ :=
  MatrixMap.conj (σ.M ^ (-1 / 2 : ℝ)).mat

lemma Gamma_inv_map_eq (σ : MState d) (X : Matrix d d ℂ) :
    Gamma_inv_map σ X = Gamma_inv σ X := by
  dsimp [Gamma_inv_map, Gamma_inv, MatrixMap.conj]
  rw [(σ.M ^ (-1 / 2 : ℝ)).H.eq]

lemma Gamma_inv_map_CP (σ : MState d) : (Gamma_inv_map σ).IsCompletelyPositive := by
  simpa [Gamma_inv_map] using MatrixMap.conj_isCompletelyPositive ((σ.M ^ (-1 / 2 : ℝ)).mat)

/-- `T` as a linear map. -/
noncomputable def T_map (σ : MState d) (Φ : CPTPMap d d₂) : MatrixMap d d₂ ℂ :=
  { toFun := fun X => T_op Φ σ X
    map_add' := fun X Y => by
      unfold T_op Gamma_inv Gamma
      simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := fun c X => by
      unfold T_op Gamma_inv Gamma
      simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc] }

lemma T_map_eq_comp (σ : MState d) (Φ : CPTPMap d d₂) :
    T_map σ Φ = (Gamma_inv_map (Φ σ)).comp (Φ.map.comp (Gamma_map σ)) := by
  ext X
  simp [T_map, T_op, Gamma_map_eq, Gamma_inv_map_eq]

lemma T_is_CP (σ : MState d) (Φ : CPTPMap d d₂) :
    (T_map σ Φ).IsCompletelyPositive := by
  rw [T_map_eq_comp]
  apply MatrixMap.IsCompletelyPositive.comp
  · apply MatrixMap.IsCompletelyPositive.comp
    · exact Gamma_map_CP σ
    · exact Φ.cp
  · exact Gamma_inv_map_CP (Φ σ)

lemma T_is_positive (σ : MState d) (Φ : CPTPMap d d₂) :
    (T_map σ Φ).IsPositive := by
  exact (T_is_CP σ Φ).IsPositive

/-- `Γ_σ(1) = σ`. -/
lemma Gamma_one (σ : MState d) : Gamma σ 1 = σ.M.mat := by
  unfold Gamma
  simpa [Matrix.mul_assoc] using HermitianMat.pow_half_mul (A := σ.M) σ.zero_le

/-- `Γ_σ⁻¹(σ) = 1` for positive definite `σ`. -/
lemma Gamma_inv_self (σ : MState d) (hσ : σ.m.PosDef) :
    Gamma_inv σ σ.M.mat = 1 := by
  have h :=
    congrArg HermitianMat.mat (HermitianMat.sandwich_self (B := σ.M) hσ)
  simpa [Gamma_inv, HermitianMat.conj_apply_mat, Matrix.mul_assoc] using h

/-- The matrix of the output state is the map applied to the input matrix. -/
lemma CPTPMap_apply_MState_M (Φ : CPTPMap d d₂) (σ : MState d) :
    (Φ σ).M.mat = Φ.map σ.M.mat := by
  rfl

/-- The operator `T` is unital whenever `Φ(σ)` is positive definite. -/
theorem T_map_unital (σ : MState d) (Φ : CPTPMap d d₂) (hΦσ : (Φ σ).m.PosDef) :
    (T_map σ Φ) 1 = 1 := by
  dsimp [T_map, T_op]
  rw [Gamma_one σ, ← CPTPMap_apply_MState_M, Gamma_inv_self (Φ σ) hΦσ]

/-- The block matrix `[[Y†Y, Y†X], [X†Y, X†X]]` is positive semidefinite. -/
theorem block_matrix_posSemidef {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (X : Matrix k n ℂ) (Y : Matrix k m ℂ) :
    (Matrix.fromBlocks (Yᴴ * Y) (Yᴴ * X) (Xᴴ * Y) (Xᴴ * X)).PosSemidef := by
  set Z : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
    Matrix.fromBlocks (Yᴴ * Y) (Yᴴ * X) (Xᴴ * Y) (Xᴴ * X)
  have hZ : Z = (Matrix.fromBlocks (o := k) Y X 0 0)ᴴ * Matrix.fromBlocks Y X 0 0 := by
    ext i j
    cases i <;> cases j <;> simp [Z, Matrix.fromBlocks_multiply, Matrix.mul_apply]
  rw [hZ]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem block_matrix_one_posSemidef {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (X : Matrix m n ℂ) :
    (Matrix.fromBlocks 1 X Xᴴ (Xᴴ * X)).PosSemidef := by
  simpa using block_matrix_posSemidef X (1 : Matrix m m ℂ)

-- The full sandwiched Rényi data processing inequality belongs here, but the current development
-- still lacks the weighted Schatten interpolation / ALT layer needed for a proof.

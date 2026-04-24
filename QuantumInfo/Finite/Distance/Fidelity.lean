/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

noncomputable section

open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] (ρ σ : MState d)

--We put all of the fidelity defs and theorems in the MState namespace so that they have the
--nice . syntax, i.e. `ρ.fidelity σ = 1 ↔ ρ = σ`.
namespace MState

/-- The fidelity of two quantum states. This is the quantum version of the Bhattacharyya coefficient. -/
def fidelity (ρ σ : MState d) : ℝ :=
  ((σ.M.conj ρ.pos.sqrt) ^ (1/2 : ℝ)).trace

theorem fidelity_ge_zero : 0 ≤ fidelity ρ σ := by
  -- Apply `HermitianMat.trace_nonneg` to the term inside the square root.
    have h_trace_nonneg : 0 ≤ (σ.M.conj ρ.pos.sqrt) ^ (1 / 2 : ℝ) := by
      apply HermitianMat.rpow_nonneg
      apply HermitianMat.conj_nonneg _ σ.zero_le
    -- Apply the fact that the trace of a positive semidefinite matrix is non-negative.
    apply HermitianMat.trace_nonneg; assumption

--PULLOUT, CLEANUP
/-
The square root of the positive semidefinite matrix of a state `ρ` is equal to `ρ` raised to the power of 1/2.
-/
theorem MState.pos_sqrt_eq_rpow {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    ρ.pos.sqrt = (ρ.M ^ (1/2 : ℝ)).mat := by
  symm
  convert ( ρ.pos.isHermitian.cfc_eq _ ) using 1;
  refine' congr_arg₂ _ ( congr_arg₂ _ rfl _ ) rfl;
  ext i;
  norm_num [ ← Real.sqrt_eq_rpow ] ;

/-- A state has perfect fidelity with itself. -/
theorem fidelity_self_eq_one : fidelity ρ ρ = 1 := by
  -- Now use the given definition to simplify the expression.
    have h_simp : ((ρ.M.conj (ρ.pos.sqrt)) ^ (1/2 : ℝ)).trace = ((ρ.M.conj ((ρ.M ^ (1/2 : ℝ)).mat)) ^ (1/2 : ℝ)).trace := by
      rw [ MState.pos_sqrt_eq_rpow ];
    have h_simp2 : (ρ.M.conj ((ρ.M ^ (1/2 : ℝ)).mat)) = ρ.M ^ (1 + 2 * (1/2) : ℝ) := by
      convert HermitianMat.conj_rpow _ _ _;
      · norm_num;
      · exact ρ.zero_le;
      · norm_num;
      · norm_num;
    have h_simp3 : ((ρ.M ^ (1 + 2 * (1/2) : ℝ)) ^ (1/2 : ℝ)) = ρ.M ^ (1 : ℝ) := by
      rw [ ← HermitianMat.rpow_mul ]
      norm_num
      exact ρ.zero_le
    unfold MState.fidelity; aesop;

private theorem fidelity_eq_traceNorm_half_mul (ρ σ : MState d) :
    fidelity ρ σ = (((σ.M ^ (1/2 : ℝ)).mat) * ((ρ.M ^ (1/2 : ℝ)).mat)).traceNorm := by
  open MatrixOrder in
  let X : Matrix d d ℂ := ((σ.M ^ (1/2 : ℝ)).mat) * ((ρ.M ^ (1/2 : ℝ)).mat)
  let P : HermitianMat d ℂ := σ.M.conj ρ.pos.sqrt
  have hP_nonneg : 0 ≤ P := by
    simpa [P] using HermitianMat.conj_nonneg ρ.pos.sqrt σ.zero_le
  have hX : Xᴴ * X = P.mat := by
    calc
      Xᴴ * X
          = ((ρ.M ^ (1/2 : ℝ)).mat) *
              (((σ.M ^ (1/2 : ℝ)).mat) * (((σ.M ^ (1/2 : ℝ)).mat) * ((ρ.M ^ (1/2 : ℝ)).mat))) := by
              simp [X, Matrix.conjTranspose_mul, ((ρ.M ^ (1/2 : ℝ)).H.eq),
                ((σ.M ^ (1/2 : ℝ)).H.eq), Matrix.mul_assoc]
      _ = ((ρ.M ^ (1/2 : ℝ)).mat) *
            ((((σ.M ^ (1/2 : ℝ)).mat) * ((σ.M ^ (1/2 : ℝ)).mat)) * ((ρ.M ^ (1/2 : ℝ)).mat)) := by
              simp [Matrix.mul_assoc]
      _ = ((ρ.M ^ (1/2 : ℝ)).mat) * (σ.M.mat * ((ρ.M ^ (1/2 : ℝ)).mat)) := by
              rw [HermitianMat.pow_half_mul σ.zero_le]
      _ = P.mat := by
              simp [P, MState.pos_sqrt_eq_rpow, HermitianMat.conj_apply_mat, Matrix.mul_assoc]
  have hpow_eq : P ^ (1/2 : ℝ) = P.cfc Real.sqrt := by
    rw [HermitianMat.rpow_eq_cfc]
    exact P.cfc_congr_of_zero_le hP_nonneg (fun x hx => by rw [Real.sqrt_eq_rpow])
  have hcfc : _root_.cfc Real.sqrt P.mat = CFC.sqrt P.mat := by
    rw [← cfcₙ_eq_cfc, ← CFC.sqrt_eq_real_sqrt P.mat
      (show 0 ≤ P.mat by
        exact Matrix.nonneg_iff_posSemidef.mpr (HermitianMat.zero_le_iff.mp hP_nonneg))]
  have hmat_eq : (P ^ (1/2 : ℝ)).mat = CFC.sqrt (Xᴴ * X) := by
    rw [hpow_eq, HermitianMat.mat_cfc, hcfc, hX]
  unfold MState.fidelity Matrix.traceNorm
  rw [MState.pos_sqrt_eq_rpow, HermitianMat.trace_eq_re_trace]
  have hPdef : σ.M.conj ((ρ.M ^ (1/2 : ℝ)).mat) = P := by
    change σ.M.conj ((ρ.M ^ (1/2 : ℝ)).mat) = σ.M.conj ρ.pos.sqrt
    rw [MState.pos_sqrt_eq_rpow]
  rw [hPdef, hmat_eq]

--TODO: Real.arccos ∘ fidelity forms a metric (triangle inequality), the Fubini–Study metric.
--Matches with classical (squared) Bhattacharyya coefficient
--Invariance under unitaries
--Uhlmann's theorem
-- Symmetry follows from trace-norm invariance under conjugate transpose; restore once that
-- helper is part of the trace-norm API again.

end MState
